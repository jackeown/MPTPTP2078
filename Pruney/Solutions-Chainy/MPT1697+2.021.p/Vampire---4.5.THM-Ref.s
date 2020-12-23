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
% DateTime   : Thu Dec  3 13:17:29 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  292 ( 728 expanded)
%              Number of leaves         :   67 ( 343 expanded)
%              Depth                    :   16
%              Number of atoms          : 1533 (3332 expanded)
%              Number of equality atoms :  185 ( 526 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f939,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f171,f200,f205,f212,f217,f239,f246,f263,f280,f285,f291,f297,f301,f307,f319,f327,f347,f367,f375,f399,f405,f415,f425,f433,f454,f467,f480,f490,f504,f547,f554,f563,f603,f638,f848,f858,f938])).

fof(f938,plain,
    ( ~ spl6_74
    | ~ spl6_6
    | spl6_16
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f937,f396,f299,f295,f243,f202,f168,f120,f542])).

fof(f542,plain,
    ( spl6_74
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f120,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f168,plain,
    ( spl6_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f202,plain,
    ( spl6_22
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f243,plain,
    ( spl6_28
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f295,plain,
    ( spl6_34
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f299,plain,
    ( spl6_35
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f396,plain,
    ( spl6_51
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f937,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f936,f245])).

fof(f245,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f243])).

fof(f936,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f935,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f935,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f934,f398])).

fof(f398,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f396])).

fof(f934,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f933,f269])).

fof(f269,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK5,X2),X3) = k7_relat_1(sK5,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ spl6_22 ),
    inference(resolution,[],[f87,f204])).

fof(f204,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f76,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f933,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_34
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f932,f296])).

fof(f296,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f932,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f931,f265])).

fof(f265,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f77,f65])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f931,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f170,f300])).

fof(f300,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f170,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f858,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_81
    | ~ spl6_75
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f857,f635,f560,f396,f299,f295,f202,f197,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f551,f600,f95,f160])).

fof(f160,plain,
    ( spl6_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f95,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f600,plain,
    ( spl6_81
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f551,plain,
    ( spl6_75
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f145,plain,
    ( spl6_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f150,plain,
    ( spl6_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f155,plain,
    ( spl6_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f130,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f135,plain,
    ( spl6_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f140,plain,
    ( spl6_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f125,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f105,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f110,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f100,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f197,plain,
    ( spl6_21
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f560,plain,
    ( spl6_76
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f635,plain,
    ( spl6_85
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f857,plain,
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(trivial_inequality_removal,[],[f856])).

fof(f856,plain,
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f855,f562])).

fof(f562,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f560])).

fof(f855,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK4,sK2),sK3)
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f854,f268])).

fof(f268,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK4,X0),X1) = k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl6_21 ),
    inference(resolution,[],[f87,f199])).

fof(f199,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f197])).

fof(f854,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
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
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f853,f59])).

fof(f853,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3)
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
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f852,f398])).

fof(f852,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3)
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
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f851,f269])).

fof(f851,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
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
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f850,f296])).

fof(f850,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
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
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f849,f265])).

fof(f849,plain,
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
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f823,f300])).

fof(f823,plain,
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
    | ~ spl6_85 ),
    inference(resolution,[],[f637,f91])).

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
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f637,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f635])).

fof(f848,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_81
    | ~ spl6_75
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f847,f635,f560,f396,f299,f295,f202,f197,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f551,f600,f95,f164])).

fof(f164,plain,
    ( spl6_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f847,plain,
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(trivial_inequality_removal,[],[f846])).

fof(f846,plain,
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f845,f562])).

fof(f845,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK4,sK2),sK3)
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
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f844,f268])).

fof(f844,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
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
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f843,f59])).

fof(f843,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3)
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
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_51
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f842,f398])).

fof(f842,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3)
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
    | ~ spl6_22
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f841,f269])).

fof(f841,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
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
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f840,f296])).

fof(f840,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
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
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f839,f265])).

fof(f839,plain,
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
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f822,f300])).

fof(f822,plain,
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
    | ~ spl6_85 ),
    inference(resolution,[],[f637,f92])).

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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f25])).

% (25854)Refutation not found, incomplete strategy% (25854)------------------------------
% (25854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f638,plain,
    ( spl6_85
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f633,f488,f130,f135,f140,f635])).

fof(f488,plain,
    ( spl6_66
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f633,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_8
    | ~ spl6_66 ),
    inference(resolution,[],[f489,f132])).

fof(f132,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f489,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f488])).

fof(f603,plain,
    ( spl6_81
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f598,f452,f130,f135,f140,f600])).

fof(f452,plain,
    ( spl6_61
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f598,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_8
    | ~ spl6_61 ),
    inference(resolution,[],[f453,f132])).

fof(f453,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f452])).

fof(f563,plain,
    ( spl6_76
    | ~ spl6_57
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f556,f542,f430,f560])).

fof(f430,plain,
    ( spl6_57
  <=> k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f556,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl6_57
    | ~ spl6_74 ),
    inference(backward_demodulation,[],[f432,f544])).

fof(f544,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f542])).

fof(f432,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f430])).

fof(f554,plain,
    ( spl6_75
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f549,f423,f130,f135,f140,f551])).

fof(f423,plain,
    ( spl6_56
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f549,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(resolution,[],[f424,f132])).

fof(f424,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f423])).

fof(f547,plain,
    ( spl6_74
    | ~ spl6_21
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f546,f501,f197,f542])).

fof(f501,plain,
    ( spl6_68
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f546,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f537,f59])).

fof(f537,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_68 ),
    inference(superposition,[],[f426,f503])).

fof(f503,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f501])).

fof(f426,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_21 ),
    inference(superposition,[],[f268,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f504,plain,
    ( spl6_68
    | ~ spl6_38
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f492,f408,f317,f501])).

fof(f317,plain,
    ( spl6_38
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f408,plain,
    ( spl6_53
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f492,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_38
    | ~ spl6_53 ),
    inference(resolution,[],[f410,f318])).

fof(f318,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X1) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f317])).

fof(f410,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f408])).

fof(f490,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_66
    | ~ spl6_11
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f482,f373,f145,f488,f100,f155,f125,f150,f120])).

fof(f373,plain,
    ( spl6_48
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f482,plain,
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
    | ~ spl6_48 ),
    inference(resolution,[],[f374,f147])).

fof(f147,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f374,plain,
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
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f373])).

fof(f480,plain,
    ( spl6_54
    | ~ spl6_22
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f479,f464,f260,f202,f412])).

fof(f412,plain,
    ( spl6_54
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f260,plain,
    ( spl6_30
  <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f464,plain,
    ( spl6_62
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f479,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f478,f262])).

fof(f262,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f260])).

fof(f478,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(superposition,[],[f222,f466])).

fof(f466,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f464])).

fof(f222,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK5,X1)) = k9_relat_1(sK5,X1)
    | ~ spl6_22 ),
    inference(resolution,[],[f67,f204])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f467,plain,
    ( spl6_62
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f462,f396,f243,f202,f464])).

fof(f462,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f461,f59])).

fof(f461,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f459,f398])).

fof(f459,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),sK3)
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(superposition,[],[f269,f245])).

fof(f454,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_61
    | ~ spl6_11
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f446,f345,f145,f452,f100,f155,f125,f150,f120])).

fof(f345,plain,
    ( spl6_43
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f446,plain,
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
    | ~ spl6_43 ),
    inference(resolution,[],[f346,f147])).

fof(f346,plain,
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
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f345])).

fof(f433,plain,
    ( spl6_57
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f427,f243,f197,f430])).

fof(f427,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(superposition,[],[f268,f245])).

fof(f425,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_56
    | ~ spl6_11
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f417,f325,f145,f423,f100,f155,f125,f150,f120])).

fof(f325,plain,
    ( spl6_39
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f417,plain,
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
    | ~ spl6_39 ),
    inference(resolution,[],[f326,f147])).

fof(f326,plain,
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
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f325])).

fof(f415,plain,
    ( spl6_53
    | ~ spl6_54
    | ~ spl6_22
    | ~ spl6_36
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f406,f402,f304,f202,f412,f408])).

fof(f304,plain,
    ( spl6_36
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f402,plain,
    ( spl6_52
  <=> k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f406,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | r1_xboole_0(sK3,sK2)
    | ~ spl6_22
    | ~ spl6_36
    | ~ spl6_52 ),
    inference(superposition,[],[f356,f404])).

fof(f404,plain,
    ( k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f402])).

fof(f356,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(sK3,X1) )
    | ~ spl6_22
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f251,f306])).

fof(f306,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f304])).

fof(f251,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(k1_relat_1(sK5),X1) )
    | ~ spl6_22 ),
    inference(resolution,[],[f69,f204])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f405,plain,
    ( spl6_52
    | ~ spl6_22
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f400,f396,f202,f402])).

fof(f400,plain,
    ( k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_51 ),
    inference(superposition,[],[f222,f398])).

fof(f399,plain,
    ( spl6_51
    | ~ spl6_27
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f394,f365,f236,f396])).

fof(f236,plain,
    ( spl6_27
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f365,plain,
    ( spl6_47
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f394,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_27
    | ~ spl6_47 ),
    inference(resolution,[],[f366,f238])).

fof(f238,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f366,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X1) )
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f365])).

fof(f375,plain,
    ( spl6_1
    | spl6_4
    | spl6_48
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f368,f105,f373,f110,f95])).

fof(f368,plain,
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
    inference(resolution,[],[f83,f107])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f105])).

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

fof(f367,plain,
    ( ~ spl6_22
    | spl6_47
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f358,f304,f365,f202])).

fof(f358,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X1) )
    | ~ spl6_36 ),
    inference(superposition,[],[f63,f306])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f347,plain,
    ( spl6_1
    | spl6_4
    | spl6_43
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f340,f105,f345,f110,f95])).

fof(f340,plain,
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
    inference(resolution,[],[f82,f107])).

fof(f82,plain,(
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

fof(f327,plain,
    ( spl6_1
    | spl6_4
    | spl6_39
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f320,f105,f325,f110,f95])).

fof(f320,plain,
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
    inference(resolution,[],[f81,f107])).

fof(f81,plain,(
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

fof(f319,plain,
    ( ~ spl6_21
    | spl6_38
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f310,f288,f317,f197])).

fof(f288,plain,
    ( spl6_33
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f310,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X1) )
    | ~ spl6_33 ),
    inference(superposition,[],[f63,f290])).

fof(f290,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f288])).

fof(f307,plain,
    ( ~ spl6_22
    | spl6_36
    | ~ spl6_24
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f302,f282,f214,f304,f202])).

fof(f214,plain,
    ( spl6_24
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f282,plain,
    ( spl6_32
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f302,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_32 ),
    inference(resolution,[],[f284,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f284,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f282])).

fof(f301,plain,
    ( spl6_35
    | ~ spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f293,f145,f155,f299])).

fof(f293,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f80,f147])).

fof(f80,plain,(
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

fof(f297,plain,
    ( spl6_34
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f292,f130,f140,f295])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f80,f132])).

fof(f291,plain,
    ( ~ spl6_21
    | spl6_33
    | ~ spl6_23
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f286,f277,f209,f288,f197])).

fof(f209,plain,
    ( spl6_23
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f277,plain,
    ( spl6_31
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f286,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_31 ),
    inference(resolution,[],[f279,f73])).

fof(f279,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f277])).

fof(f285,plain,
    ( spl6_32
    | ~ spl6_12
    | ~ spl6_13
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f275,f145,f100,f155,f150,f282])).

fof(f275,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f66,f147])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f280,plain,
    ( spl6_31
    | ~ spl6_9
    | ~ spl6_10
    | spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f274,f130,f100,f140,f135,f277])).

fof(f274,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f66,f132])).

fof(f263,plain,
    ( spl6_30
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f253,f202,f260])).

fof(f253,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_22 ),
    inference(resolution,[],[f249,f204])).

fof(f249,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f68,f219])).

fof(f219,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f86,f84])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f65])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f246,plain,
    ( spl6_28
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f241,f236,f243])).

fof(f241,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_27 ),
    inference(resolution,[],[f238,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f75,f65])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f239,plain,
    ( spl6_4
    | spl6_27
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f232,f115,f125,f236,f110])).

% (25874)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f115,plain,
    ( spl6_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f232,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f71,f117])).

fof(f117,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f217,plain,
    ( spl6_24
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f207,f145,f214])).

fof(f207,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f79,f147])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f212,plain,
    ( spl6_23
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f206,f130,f209])).

fof(f206,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f79,f132])).

fof(f205,plain,
    ( spl6_22
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f195,f145,f202])).

fof(f195,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(resolution,[],[f78,f147])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f200,plain,
    ( spl6_21
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f194,f130,f197])).

fof(f194,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f78,f132])).

fof(f171,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f44,f168,f164,f160])).

fof(f44,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    spl6_13 ),
    inference(avatar_split_clause,[],[f45,f155])).

fof(f45,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f153,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f46,f150])).

fof(f46,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f148,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f143,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f48,f140])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f138,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f49,f135])).

fof(f49,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f133,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f50,f130])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f128,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f51,f125])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f52,f120])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f53,f115])).

fof(f53,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f55,f105])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f56,f100])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f57,f95])).

fof(f57,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (25853)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.48  % (25861)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (25861)Refutation not found, incomplete strategy% (25861)------------------------------
% 0.20/0.49  % (25861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25861)Memory used [KB]: 10746
% 0.20/0.49  % (25861)Time elapsed: 0.085 s
% 0.20/0.49  % (25861)------------------------------
% 0.20/0.49  % (25861)------------------------------
% 0.20/0.52  % (25857)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (25868)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (25869)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (25852)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (25858)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (25846)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (25847)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (25849)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (25867)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (25848)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (25844)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.54  % (25850)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.54  % (25866)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.54  % (25872)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.54  % (25845)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.54  % (25863)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.54  % (25859)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.54  % (25860)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (25864)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (25871)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (25873)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (25851)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (25854)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (25870)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (25855)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (25856)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (25865)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.55/0.56  % (25862)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.57  % (25866)Refutation not found, incomplete strategy% (25866)------------------------------
% 1.55/0.57  % (25866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (25866)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (25866)Memory used [KB]: 11513
% 1.55/0.57  % (25866)Time elapsed: 0.171 s
% 1.55/0.57  % (25866)------------------------------
% 1.55/0.57  % (25866)------------------------------
% 1.55/0.58  % (25860)Refutation found. Thanks to Tanya!
% 1.55/0.58  % SZS status Theorem for theBenchmark
% 1.55/0.58  % SZS output start Proof for theBenchmark
% 1.55/0.58  fof(f939,plain,(
% 1.55/0.58    $false),
% 1.55/0.58    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f171,f200,f205,f212,f217,f239,f246,f263,f280,f285,f291,f297,f301,f307,f319,f327,f347,f367,f375,f399,f405,f415,f425,f433,f454,f467,f480,f490,f504,f547,f554,f563,f603,f638,f848,f858,f938])).
% 1.55/0.58  fof(f938,plain,(
% 1.55/0.58    ~spl6_74 | ~spl6_6 | spl6_16 | ~spl6_22 | ~spl6_28 | ~spl6_34 | ~spl6_35 | ~spl6_51),
% 1.55/0.58    inference(avatar_split_clause,[],[f937,f396,f299,f295,f243,f202,f168,f120,f542])).
% 1.55/0.58  fof(f542,plain,(
% 1.55/0.58    spl6_74 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 1.55/0.58  fof(f120,plain,(
% 1.55/0.58    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.55/0.58  fof(f168,plain,(
% 1.55/0.58    spl6_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.55/0.58  fof(f202,plain,(
% 1.55/0.58    spl6_22 <=> v1_relat_1(sK5)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.55/0.58  fof(f243,plain,(
% 1.55/0.58    spl6_28 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.55/0.58  fof(f295,plain,(
% 1.55/0.58    spl6_34 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.55/0.58  fof(f299,plain,(
% 1.55/0.58    spl6_35 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.55/0.58  fof(f396,plain,(
% 1.55/0.58    spl6_51 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.55/0.58  fof(f937,plain,(
% 1.55/0.58    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_22 | ~spl6_28 | ~spl6_34 | ~spl6_35 | ~spl6_51)),
% 1.55/0.58    inference(forward_demodulation,[],[f936,f245])).
% 1.55/0.58  fof(f245,plain,(
% 1.55/0.58    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_28),
% 1.55/0.58    inference(avatar_component_clause,[],[f243])).
% 1.55/0.58  fof(f936,plain,(
% 1.55/0.58    k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51)),
% 1.55/0.58    inference(forward_demodulation,[],[f935,f59])).
% 1.55/0.58  fof(f59,plain,(
% 1.55/0.58    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f7])).
% 1.55/0.58  fof(f7,axiom,(
% 1.55/0.58    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 1.55/0.58  fof(f935,plain,(
% 1.55/0.58    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3) | (~spl6_6 | spl6_16 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51)),
% 1.55/0.58    inference(forward_demodulation,[],[f934,f398])).
% 1.55/0.58  fof(f398,plain,(
% 1.55/0.58    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_51),
% 1.55/0.58    inference(avatar_component_clause,[],[f396])).
% 1.55/0.58  fof(f934,plain,(
% 1.55/0.58    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3) | (~spl6_6 | spl6_16 | ~spl6_22 | ~spl6_34 | ~spl6_35)),
% 1.55/0.58    inference(forward_demodulation,[],[f933,f269])).
% 1.55/0.58  fof(f269,plain,(
% 1.55/0.58    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK5,X2),X3) = k7_relat_1(sK5,k1_setfam_1(k2_tarski(X2,X3)))) ) | ~spl6_22),
% 1.55/0.58    inference(resolution,[],[f87,f204])).
% 1.55/0.58  fof(f204,plain,(
% 1.55/0.58    v1_relat_1(sK5) | ~spl6_22),
% 1.55/0.58    inference(avatar_component_clause,[],[f202])).
% 1.55/0.58  fof(f87,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.55/0.58    inference(definition_unfolding,[],[f76,f65])).
% 1.55/0.58  fof(f65,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.55/0.58  fof(f76,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f36])).
% 1.55/0.58  fof(f36,plain,(
% 1.55/0.58    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.55/0.58    inference(ennf_transformation,[],[f6])).
% 1.55/0.58  fof(f6,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.55/0.58  fof(f933,plain,(
% 1.55/0.58    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_34 | ~spl6_35)),
% 1.55/0.58    inference(forward_demodulation,[],[f932,f296])).
% 1.55/0.58  fof(f296,plain,(
% 1.55/0.58    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_34),
% 1.55/0.58    inference(avatar_component_clause,[],[f295])).
% 1.55/0.58  fof(f932,plain,(
% 1.55/0.58    k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_35)),
% 1.55/0.58    inference(forward_demodulation,[],[f931,f265])).
% 1.55/0.58  fof(f265,plain,(
% 1.55/0.58    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl6_6),
% 1.55/0.58    inference(resolution,[],[f88,f122])).
% 1.55/0.58  fof(f122,plain,(
% 1.55/0.58    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 1.55/0.58    inference(avatar_component_clause,[],[f120])).
% 1.55/0.58  fof(f88,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.55/0.58    inference(definition_unfolding,[],[f77,f65])).
% 1.55/0.58  fof(f77,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f37])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.55/0.58  fof(f931,plain,(
% 1.55/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_16 | ~spl6_35)),
% 1.55/0.58    inference(forward_demodulation,[],[f170,f300])).
% 1.55/0.58  fof(f300,plain,(
% 1.55/0.58    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_35),
% 1.55/0.58    inference(avatar_component_clause,[],[f299])).
% 1.55/0.58  fof(f170,plain,(
% 1.55/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_16),
% 1.55/0.58    inference(avatar_component_clause,[],[f168])).
% 1.55/0.58  fof(f858,plain,(
% 1.55/0.58    spl6_14 | spl6_1 | ~spl6_81 | ~spl6_75 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_76 | ~spl6_85),
% 1.55/0.58    inference(avatar_split_clause,[],[f857,f635,f560,f396,f299,f295,f202,f197,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f551,f600,f95,f160])).
% 1.55/0.58  fof(f160,plain,(
% 1.55/0.58    spl6_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.55/0.58  fof(f95,plain,(
% 1.55/0.58    spl6_1 <=> v1_xboole_0(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.55/0.58  fof(f600,plain,(
% 1.55/0.58    spl6_81 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 1.55/0.58  fof(f551,plain,(
% 1.55/0.58    spl6_75 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 1.55/0.58  fof(f145,plain,(
% 1.55/0.58    spl6_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.55/0.58  fof(f150,plain,(
% 1.55/0.58    spl6_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.55/0.58  fof(f155,plain,(
% 1.55/0.58    spl6_13 <=> v1_funct_1(sK5)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.55/0.58  fof(f130,plain,(
% 1.55/0.58    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.55/0.58  fof(f135,plain,(
% 1.55/0.58    spl6_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.55/0.58  fof(f140,plain,(
% 1.55/0.58    spl6_10 <=> v1_funct_1(sK4)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.55/0.58  fof(f125,plain,(
% 1.55/0.58    spl6_7 <=> v1_xboole_0(sK3)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.55/0.58  fof(f105,plain,(
% 1.55/0.58    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.55/0.58  fof(f110,plain,(
% 1.55/0.58    spl6_4 <=> v1_xboole_0(sK2)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.55/0.58  fof(f100,plain,(
% 1.55/0.58    spl6_2 <=> v1_xboole_0(sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.55/0.58  fof(f197,plain,(
% 1.55/0.58    spl6_21 <=> v1_relat_1(sK4)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.55/0.58  fof(f560,plain,(
% 1.55/0.58    spl6_76 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 1.55/0.58  fof(f635,plain,(
% 1.55/0.58    spl6_85 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 1.55/0.58  fof(f857,plain,(
% 1.55/0.58    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_76 | ~spl6_85)),
% 1.55/0.58    inference(trivial_inequality_removal,[],[f856])).
% 1.55/0.58  fof(f856,plain,(
% 1.55/0.58    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_76 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f855,f562])).
% 1.55/0.58  fof(f562,plain,(
% 1.55/0.58    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | ~spl6_76),
% 1.55/0.58    inference(avatar_component_clause,[],[f560])).
% 1.55/0.58  fof(f855,plain,(
% 1.55/0.58    k1_xboole_0 != k7_relat_1(k7_relat_1(sK4,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f854,f268])).
% 1.55/0.58  fof(f268,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK4,X0),X1) = k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl6_21),
% 1.55/0.58    inference(resolution,[],[f87,f199])).
% 1.55/0.58  fof(f199,plain,(
% 1.55/0.58    v1_relat_1(sK4) | ~spl6_21),
% 1.55/0.58    inference(avatar_component_clause,[],[f197])).
% 1.55/0.58  fof(f854,plain,(
% 1.55/0.58    k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f853,f59])).
% 1.55/0.58  fof(f853,plain,(
% 1.55/0.58    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f852,f398])).
% 1.55/0.58  fof(f852,plain,(
% 1.55/0.58    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f851,f269])).
% 1.55/0.58  fof(f851,plain,(
% 1.55/0.58    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_34 | ~spl6_35 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f850,f296])).
% 1.55/0.58  fof(f850,plain,(
% 1.55/0.58    k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_35 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f849,f265])).
% 1.55/0.58  fof(f849,plain,(
% 1.55/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_35 | ~spl6_85)),
% 1.55/0.58    inference(forward_demodulation,[],[f823,f300])).
% 1.55/0.58  fof(f823,plain,(
% 1.55/0.58    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_85),
% 1.55/0.58    inference(resolution,[],[f637,f91])).
% 1.55/0.58  fof(f91,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.55/0.58    inference(equality_resolution,[],[f61])).
% 1.55/0.58  fof(f61,plain,(
% 1.55/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.55/0.58    inference(cnf_transformation,[],[f25])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.55/0.58    inference(flattening,[],[f24])).
% 1.55/0.58  fof(f24,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f17])).
% 1.55/0.59  fof(f17,axiom,(
% 1.55/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.55/0.59  fof(f637,plain,(
% 1.55/0.59    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_85),
% 1.55/0.59    inference(avatar_component_clause,[],[f635])).
% 1.55/0.59  fof(f848,plain,(
% 1.55/0.59    spl6_15 | spl6_1 | ~spl6_81 | ~spl6_75 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_76 | ~spl6_85),
% 1.55/0.59    inference(avatar_split_clause,[],[f847,f635,f560,f396,f299,f295,f202,f197,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f551,f600,f95,f164])).
% 1.55/0.59  fof(f164,plain,(
% 1.55/0.59    spl6_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.55/0.59  fof(f847,plain,(
% 1.55/0.59    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_76 | ~spl6_85)),
% 1.55/0.59    inference(trivial_inequality_removal,[],[f846])).
% 1.55/0.59  fof(f846,plain,(
% 1.55/0.59    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_76 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f845,f562])).
% 1.55/0.59  fof(f845,plain,(
% 1.55/0.59    k1_xboole_0 != k7_relat_1(k7_relat_1(sK4,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_21 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f844,f268])).
% 1.55/0.59  fof(f844,plain,(
% 1.55/0.59    k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f843,f59])).
% 1.55/0.59  fof(f843,plain,(
% 1.55/0.59    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_51 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f842,f398])).
% 1.55/0.59  fof(f842,plain,(
% 1.55/0.59    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_22 | ~spl6_34 | ~spl6_35 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f841,f269])).
% 1.55/0.59  fof(f841,plain,(
% 1.55/0.59    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_34 | ~spl6_35 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f840,f296])).
% 1.55/0.59  fof(f840,plain,(
% 1.55/0.59    k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_35 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f839,f265])).
% 1.55/0.59  fof(f839,plain,(
% 1.55/0.59    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_35 | ~spl6_85)),
% 1.55/0.59    inference(forward_demodulation,[],[f822,f300])).
% 1.55/0.59  fof(f822,plain,(
% 1.55/0.59    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_85),
% 1.55/0.59    inference(resolution,[],[f637,f92])).
% 1.55/0.59  fof(f92,plain,(
% 1.55/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.55/0.59    inference(equality_resolution,[],[f60])).
% 1.55/0.60  fof(f60,plain,(
% 1.55/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.55/0.60    inference(cnf_transformation,[],[f25])).
% 1.55/0.60  % (25854)Refutation not found, incomplete strategy% (25854)------------------------------
% 1.55/0.60  % (25854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  fof(f638,plain,(
% 1.55/0.60    spl6_85 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_66),
% 1.55/0.60    inference(avatar_split_clause,[],[f633,f488,f130,f135,f140,f635])).
% 1.55/0.60  fof(f488,plain,(
% 1.55/0.60    spl6_66 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 1.55/0.60  fof(f633,plain,(
% 1.55/0.60    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_8 | ~spl6_66)),
% 1.55/0.60    inference(resolution,[],[f489,f132])).
% 1.55/0.60  fof(f132,plain,(
% 1.55/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_8),
% 1.55/0.60    inference(avatar_component_clause,[],[f130])).
% 1.55/0.60  fof(f489,plain,(
% 1.55/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl6_66),
% 1.55/0.60    inference(avatar_component_clause,[],[f488])).
% 1.55/0.60  fof(f603,plain,(
% 1.55/0.60    spl6_81 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_61),
% 1.55/0.60    inference(avatar_split_clause,[],[f598,f452,f130,f135,f140,f600])).
% 1.55/0.60  fof(f452,plain,(
% 1.55/0.60    spl6_61 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 1.55/0.60  fof(f598,plain,(
% 1.55/0.60    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_8 | ~spl6_61)),
% 1.55/0.60    inference(resolution,[],[f453,f132])).
% 1.55/0.60  fof(f453,plain,(
% 1.55/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl6_61),
% 1.55/0.60    inference(avatar_component_clause,[],[f452])).
% 1.55/0.60  fof(f563,plain,(
% 1.55/0.60    spl6_76 | ~spl6_57 | ~spl6_74),
% 1.55/0.60    inference(avatar_split_clause,[],[f556,f542,f430,f560])).
% 1.55/0.60  fof(f430,plain,(
% 1.55/0.60    spl6_57 <=> k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 1.55/0.60  fof(f556,plain,(
% 1.55/0.60    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | (~spl6_57 | ~spl6_74)),
% 1.55/0.60    inference(backward_demodulation,[],[f432,f544])).
% 1.55/0.60  fof(f544,plain,(
% 1.55/0.60    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_74),
% 1.55/0.60    inference(avatar_component_clause,[],[f542])).
% 1.55/0.60  fof(f432,plain,(
% 1.55/0.60    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | ~spl6_57),
% 1.55/0.60    inference(avatar_component_clause,[],[f430])).
% 1.55/0.60  fof(f554,plain,(
% 1.55/0.60    spl6_75 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_56),
% 1.55/0.60    inference(avatar_split_clause,[],[f549,f423,f130,f135,f140,f551])).
% 1.55/0.60  fof(f423,plain,(
% 1.55/0.60    spl6_56 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 1.55/0.60  fof(f549,plain,(
% 1.55/0.60    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_56)),
% 1.55/0.60    inference(resolution,[],[f424,f132])).
% 1.55/0.60  fof(f424,plain,(
% 1.55/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl6_56),
% 1.55/0.60    inference(avatar_component_clause,[],[f423])).
% 1.55/0.60  fof(f547,plain,(
% 1.55/0.60    spl6_74 | ~spl6_21 | ~spl6_68),
% 1.55/0.60    inference(avatar_split_clause,[],[f546,f501,f197,f542])).
% 1.55/0.60  fof(f501,plain,(
% 1.55/0.60    spl6_68 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 1.55/0.60  fof(f546,plain,(
% 1.55/0.60    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_21 | ~spl6_68)),
% 1.55/0.60    inference(forward_demodulation,[],[f537,f59])).
% 1.55/0.60  fof(f537,plain,(
% 1.55/0.60    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_21 | ~spl6_68)),
% 1.55/0.60    inference(superposition,[],[f426,f503])).
% 1.55/0.60  fof(f503,plain,(
% 1.55/0.60    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_68),
% 1.55/0.60    inference(avatar_component_clause,[],[f501])).
% 1.55/0.60  fof(f426,plain,(
% 1.55/0.60    ( ! [X0] : (k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)) ) | ~spl6_21),
% 1.55/0.60    inference(superposition,[],[f268,f84])).
% 1.55/0.60  fof(f84,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f58,f65])).
% 1.55/0.60  fof(f58,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.55/0.60  fof(f504,plain,(
% 1.55/0.60    spl6_68 | ~spl6_38 | ~spl6_53),
% 1.55/0.60    inference(avatar_split_clause,[],[f492,f408,f317,f501])).
% 1.55/0.60  fof(f317,plain,(
% 1.55/0.60    spl6_38 <=> ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1))),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.55/0.60  fof(f408,plain,(
% 1.55/0.60    spl6_53 <=> r1_xboole_0(sK3,sK2)),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.55/0.60  fof(f492,plain,(
% 1.55/0.60    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_38 | ~spl6_53)),
% 1.55/0.60    inference(resolution,[],[f410,f318])).
% 1.55/0.60  fof(f318,plain,(
% 1.55/0.60    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1)) ) | ~spl6_38),
% 1.55/0.60    inference(avatar_component_clause,[],[f317])).
% 1.55/0.60  fof(f410,plain,(
% 1.55/0.60    r1_xboole_0(sK3,sK2) | ~spl6_53),
% 1.55/0.60    inference(avatar_component_clause,[],[f408])).
% 1.55/0.61  fof(f490,plain,(
% 1.55/0.61    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_66 | ~spl6_11 | ~spl6_48),
% 1.55/0.61    inference(avatar_split_clause,[],[f482,f373,f145,f488,f100,f155,f125,f150,f120])).
% 1.55/0.61  fof(f373,plain,(
% 1.55/0.61    spl6_48 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.55/0.61  fof(f482,plain,(
% 1.55/0.61    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_48)),
% 1.55/0.61    inference(resolution,[],[f374,f147])).
% 1.55/0.61  fof(f147,plain,(
% 1.55/0.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_11),
% 1.55/0.61    inference(avatar_component_clause,[],[f145])).
% 1.55/0.61  fof(f374,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_48),
% 1.55/0.61    inference(avatar_component_clause,[],[f373])).
% 1.55/0.61  fof(f480,plain,(
% 1.55/0.61    spl6_54 | ~spl6_22 | ~spl6_30 | ~spl6_62),
% 1.55/0.61    inference(avatar_split_clause,[],[f479,f464,f260,f202,f412])).
% 1.55/0.61  fof(f412,plain,(
% 1.55/0.61    spl6_54 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.55/0.61  fof(f260,plain,(
% 1.55/0.61    spl6_30 <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.55/0.61  fof(f464,plain,(
% 1.55/0.61    spl6_62 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.55/0.61  fof(f479,plain,(
% 1.55/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl6_22 | ~spl6_30 | ~spl6_62)),
% 1.55/0.61    inference(forward_demodulation,[],[f478,f262])).
% 1.55/0.61  fof(f262,plain,(
% 1.55/0.61    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl6_30),
% 1.55/0.61    inference(avatar_component_clause,[],[f260])).
% 1.55/0.61  fof(f478,plain,(
% 1.55/0.61    k9_relat_1(sK5,k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl6_22 | ~spl6_62)),
% 1.55/0.61    inference(superposition,[],[f222,f466])).
% 1.55/0.61  fof(f466,plain,(
% 1.55/0.61    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_62),
% 1.55/0.61    inference(avatar_component_clause,[],[f464])).
% 1.55/0.61  fof(f222,plain,(
% 1.55/0.61    ( ! [X1] : (k2_relat_1(k7_relat_1(sK5,X1)) = k9_relat_1(sK5,X1)) ) | ~spl6_22),
% 1.55/0.61    inference(resolution,[],[f67,f204])).
% 1.55/0.61  fof(f67,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f30])).
% 1.55/0.61  fof(f30,plain,(
% 1.55/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f8])).
% 1.55/0.61  fof(f8,axiom,(
% 1.55/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.55/0.61  fof(f467,plain,(
% 1.55/0.61    spl6_62 | ~spl6_22 | ~spl6_28 | ~spl6_51),
% 1.55/0.61    inference(avatar_split_clause,[],[f462,f396,f243,f202,f464])).
% 1.55/0.61  fof(f462,plain,(
% 1.55/0.61    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_22 | ~spl6_28 | ~spl6_51)),
% 1.55/0.61    inference(forward_demodulation,[],[f461,f59])).
% 1.55/0.61  fof(f461,plain,(
% 1.55/0.61    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k1_xboole_0,sK3) | (~spl6_22 | ~spl6_28 | ~spl6_51)),
% 1.55/0.61    inference(forward_demodulation,[],[f459,f398])).
% 1.55/0.61  fof(f459,plain,(
% 1.55/0.61    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),sK3) | (~spl6_22 | ~spl6_28)),
% 1.55/0.61    inference(superposition,[],[f269,f245])).
% 1.55/0.61  fof(f454,plain,(
% 1.55/0.61    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_61 | ~spl6_11 | ~spl6_43),
% 1.55/0.61    inference(avatar_split_clause,[],[f446,f345,f145,f452,f100,f155,f125,f150,f120])).
% 1.55/0.61  fof(f345,plain,(
% 1.55/0.61    spl6_43 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 1.55/0.61  fof(f446,plain,(
% 1.55/0.61    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_43)),
% 1.55/0.61    inference(resolution,[],[f346,f147])).
% 1.55/0.61  fof(f346,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_43),
% 1.55/0.61    inference(avatar_component_clause,[],[f345])).
% 1.55/0.61  fof(f433,plain,(
% 1.55/0.61    spl6_57 | ~spl6_21 | ~spl6_28),
% 1.55/0.61    inference(avatar_split_clause,[],[f427,f243,f197,f430])).
% 1.55/0.61  fof(f427,plain,(
% 1.55/0.61    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | (~spl6_21 | ~spl6_28)),
% 1.55/0.61    inference(superposition,[],[f268,f245])).
% 1.55/0.61  fof(f425,plain,(
% 1.55/0.61    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_56 | ~spl6_11 | ~spl6_39),
% 1.55/0.61    inference(avatar_split_clause,[],[f417,f325,f145,f423,f100,f155,f125,f150,f120])).
% 1.55/0.61  fof(f325,plain,(
% 1.55/0.61    spl6_39 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.55/0.61  fof(f417,plain,(
% 1.55/0.61    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_39)),
% 1.55/0.61    inference(resolution,[],[f326,f147])).
% 1.55/0.61  fof(f326,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_39),
% 1.55/0.61    inference(avatar_component_clause,[],[f325])).
% 1.55/0.61  fof(f415,plain,(
% 1.55/0.61    spl6_53 | ~spl6_54 | ~spl6_22 | ~spl6_36 | ~spl6_52),
% 1.55/0.61    inference(avatar_split_clause,[],[f406,f402,f304,f202,f412,f408])).
% 1.55/0.61  fof(f304,plain,(
% 1.55/0.61    spl6_36 <=> sK3 = k1_relat_1(sK5)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.55/0.61  fof(f402,plain,(
% 1.55/0.61    spl6_52 <=> k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.55/0.61  fof(f406,plain,(
% 1.55/0.61    k1_xboole_0 != k2_relat_1(k1_xboole_0) | r1_xboole_0(sK3,sK2) | (~spl6_22 | ~spl6_36 | ~spl6_52)),
% 1.55/0.61    inference(superposition,[],[f356,f404])).
% 1.55/0.61  fof(f404,plain,(
% 1.55/0.61    k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0) | ~spl6_52),
% 1.55/0.61    inference(avatar_component_clause,[],[f402])).
% 1.55/0.61  fof(f356,plain,(
% 1.55/0.61    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(sK3,X1)) ) | (~spl6_22 | ~spl6_36)),
% 1.55/0.61    inference(backward_demodulation,[],[f251,f306])).
% 1.55/0.61  fof(f306,plain,(
% 1.55/0.61    sK3 = k1_relat_1(sK5) | ~spl6_36),
% 1.55/0.61    inference(avatar_component_clause,[],[f304])).
% 1.55/0.61  fof(f251,plain,(
% 1.55/0.61    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(k1_relat_1(sK5),X1)) ) | ~spl6_22),
% 1.55/0.61    inference(resolution,[],[f69,f204])).
% 1.55/0.61  fof(f69,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f31])).
% 1.55/0.61  fof(f31,plain,(
% 1.55/0.61    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f9])).
% 1.55/0.61  fof(f9,axiom,(
% 1.55/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.55/0.61  fof(f405,plain,(
% 1.55/0.61    spl6_52 | ~spl6_22 | ~spl6_51),
% 1.55/0.61    inference(avatar_split_clause,[],[f400,f396,f202,f402])).
% 1.55/0.61  fof(f400,plain,(
% 1.55/0.61    k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0) | (~spl6_22 | ~spl6_51)),
% 1.55/0.61    inference(superposition,[],[f222,f398])).
% 1.55/0.61  fof(f399,plain,(
% 1.55/0.61    spl6_51 | ~spl6_27 | ~spl6_47),
% 1.55/0.61    inference(avatar_split_clause,[],[f394,f365,f236,f396])).
% 1.55/0.61  fof(f236,plain,(
% 1.55/0.61    spl6_27 <=> r1_xboole_0(sK2,sK3)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.55/0.61  fof(f365,plain,(
% 1.55/0.61    spl6_47 <=> ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.55/0.61  fof(f394,plain,(
% 1.55/0.61    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_27 | ~spl6_47)),
% 1.55/0.61    inference(resolution,[],[f366,f238])).
% 1.55/0.61  fof(f238,plain,(
% 1.55/0.61    r1_xboole_0(sK2,sK3) | ~spl6_27),
% 1.55/0.61    inference(avatar_component_clause,[],[f236])).
% 1.55/0.61  fof(f366,plain,(
% 1.55/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1)) ) | ~spl6_47),
% 1.55/0.61    inference(avatar_component_clause,[],[f365])).
% 1.55/0.61  fof(f375,plain,(
% 1.55/0.61    spl6_1 | spl6_4 | spl6_48 | ~spl6_3),
% 1.55/0.61    inference(avatar_split_clause,[],[f368,f105,f373,f110,f95])).
% 1.55/0.61  fof(f368,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl6_3),
% 1.55/0.61    inference(resolution,[],[f83,f107])).
% 1.55/0.61  fof(f107,plain,(
% 1.55/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_3),
% 1.55/0.61    inference(avatar_component_clause,[],[f105])).
% 1.55/0.61  fof(f83,plain,(
% 1.55/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f43,plain,(
% 1.55/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.55/0.61    inference(flattening,[],[f42])).
% 1.55/0.61  fof(f42,plain,(
% 1.55/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.55/0.61    inference(ennf_transformation,[],[f18])).
% 1.55/0.61  fof(f18,axiom,(
% 1.55/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.55/0.61  fof(f367,plain,(
% 1.55/0.61    ~spl6_22 | spl6_47 | ~spl6_36),
% 1.55/0.61    inference(avatar_split_clause,[],[f358,f304,f365,f202])).
% 1.55/0.61  fof(f358,plain,(
% 1.55/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X1)) ) | ~spl6_36),
% 1.55/0.61    inference(superposition,[],[f63,f306])).
% 1.55/0.61  fof(f63,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f26])).
% 1.55/0.61  fof(f26,plain,(
% 1.55/0.61    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.55/0.61    inference(ennf_transformation,[],[f10])).
% 1.55/0.61  fof(f10,axiom,(
% 1.55/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 1.55/0.61  fof(f347,plain,(
% 1.55/0.61    spl6_1 | spl6_4 | spl6_43 | ~spl6_3),
% 1.55/0.61    inference(avatar_split_clause,[],[f340,f105,f345,f110,f95])).
% 1.55/0.61  fof(f340,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl6_3),
% 1.55/0.61    inference(resolution,[],[f82,f107])).
% 1.55/0.61  fof(f82,plain,(
% 1.55/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f327,plain,(
% 1.55/0.61    spl6_1 | spl6_4 | spl6_39 | ~spl6_3),
% 1.55/0.61    inference(avatar_split_clause,[],[f320,f105,f325,f110,f95])).
% 1.55/0.61  fof(f320,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl6_3),
% 1.55/0.61    inference(resolution,[],[f81,f107])).
% 1.55/0.61  fof(f81,plain,(
% 1.55/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f43])).
% 1.55/0.61  fof(f319,plain,(
% 1.55/0.61    ~spl6_21 | spl6_38 | ~spl6_33),
% 1.55/0.61    inference(avatar_split_clause,[],[f310,f288,f317,f197])).
% 1.55/0.61  fof(f288,plain,(
% 1.55/0.61    spl6_33 <=> sK2 = k1_relat_1(sK4)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.55/0.61  fof(f310,plain,(
% 1.55/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X1)) ) | ~spl6_33),
% 1.55/0.61    inference(superposition,[],[f63,f290])).
% 1.55/0.61  fof(f290,plain,(
% 1.55/0.61    sK2 = k1_relat_1(sK4) | ~spl6_33),
% 1.55/0.61    inference(avatar_component_clause,[],[f288])).
% 1.55/0.61  fof(f307,plain,(
% 1.55/0.61    ~spl6_22 | spl6_36 | ~spl6_24 | ~spl6_32),
% 1.55/0.61    inference(avatar_split_clause,[],[f302,f282,f214,f304,f202])).
% 1.55/0.61  fof(f214,plain,(
% 1.55/0.61    spl6_24 <=> v4_relat_1(sK5,sK3)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.55/0.61  fof(f282,plain,(
% 1.55/0.61    spl6_32 <=> v1_partfun1(sK5,sK3)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.55/0.61  fof(f302,plain,(
% 1.55/0.61    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_32),
% 1.55/0.61    inference(resolution,[],[f284,f73])).
% 1.55/0.61  fof(f73,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f35])).
% 1.55/0.61  fof(f35,plain,(
% 1.55/0.61    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.55/0.61    inference(flattening,[],[f34])).
% 1.55/0.61  fof(f34,plain,(
% 1.55/0.61    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.55/0.61    inference(ennf_transformation,[],[f15])).
% 1.55/0.61  fof(f15,axiom,(
% 1.55/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.55/0.61  fof(f284,plain,(
% 1.55/0.61    v1_partfun1(sK5,sK3) | ~spl6_32),
% 1.55/0.61    inference(avatar_component_clause,[],[f282])).
% 1.55/0.61  fof(f301,plain,(
% 1.55/0.61    spl6_35 | ~spl6_13 | ~spl6_11),
% 1.55/0.61    inference(avatar_split_clause,[],[f293,f145,f155,f299])).
% 1.55/0.61  fof(f293,plain,(
% 1.55/0.61    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_11),
% 1.55/0.61    inference(resolution,[],[f80,f147])).
% 1.55/0.61  fof(f80,plain,(
% 1.55/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f41])).
% 1.55/0.61  fof(f41,plain,(
% 1.55/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.55/0.61    inference(flattening,[],[f40])).
% 1.55/0.61  fof(f40,plain,(
% 1.55/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.55/0.61    inference(ennf_transformation,[],[f16])).
% 1.55/0.61  fof(f16,axiom,(
% 1.55/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.55/0.61  fof(f297,plain,(
% 1.55/0.61    spl6_34 | ~spl6_10 | ~spl6_8),
% 1.55/0.61    inference(avatar_split_clause,[],[f292,f130,f140,f295])).
% 1.55/0.61  fof(f292,plain,(
% 1.55/0.61    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_8),
% 1.55/0.61    inference(resolution,[],[f80,f132])).
% 1.55/0.61  fof(f291,plain,(
% 1.55/0.61    ~spl6_21 | spl6_33 | ~spl6_23 | ~spl6_31),
% 1.55/0.61    inference(avatar_split_clause,[],[f286,f277,f209,f288,f197])).
% 1.55/0.61  fof(f209,plain,(
% 1.55/0.61    spl6_23 <=> v4_relat_1(sK4,sK2)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.55/0.61  fof(f277,plain,(
% 1.55/0.61    spl6_31 <=> v1_partfun1(sK4,sK2)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.55/0.61  fof(f286,plain,(
% 1.55/0.61    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_31),
% 1.55/0.61    inference(resolution,[],[f279,f73])).
% 1.55/0.61  fof(f279,plain,(
% 1.55/0.61    v1_partfun1(sK4,sK2) | ~spl6_31),
% 1.55/0.61    inference(avatar_component_clause,[],[f277])).
% 1.55/0.61  fof(f285,plain,(
% 1.55/0.61    spl6_32 | ~spl6_12 | ~spl6_13 | spl6_2 | ~spl6_11),
% 1.55/0.61    inference(avatar_split_clause,[],[f275,f145,f100,f155,f150,f282])).
% 1.55/0.61  fof(f275,plain,(
% 1.55/0.61    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_11),
% 1.55/0.61    inference(resolution,[],[f66,f147])).
% 1.55/0.61  fof(f66,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f29])).
% 1.55/0.61  fof(f29,plain,(
% 1.55/0.61    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.55/0.61    inference(flattening,[],[f28])).
% 1.55/0.61  fof(f28,plain,(
% 1.55/0.61    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f14])).
% 1.55/0.61  fof(f14,axiom,(
% 1.55/0.61    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.55/0.61  fof(f280,plain,(
% 1.55/0.61    spl6_31 | ~spl6_9 | ~spl6_10 | spl6_2 | ~spl6_8),
% 1.55/0.61    inference(avatar_split_clause,[],[f274,f130,f100,f140,f135,f277])).
% 1.55/0.61  fof(f274,plain,(
% 1.55/0.61    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl6_8),
% 1.55/0.61    inference(resolution,[],[f66,f132])).
% 1.55/0.61  fof(f263,plain,(
% 1.55/0.61    spl6_30 | ~spl6_22),
% 1.55/0.61    inference(avatar_split_clause,[],[f253,f202,f260])).
% 1.55/0.61  fof(f253,plain,(
% 1.55/0.61    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl6_22),
% 1.55/0.61    inference(resolution,[],[f249,f204])).
% 1.55/0.61  fof(f249,plain,(
% 1.55/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f68,f219])).
% 1.55/0.61  fof(f219,plain,(
% 1.55/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(trivial_inequality_removal,[],[f218])).
% 1.55/0.61  fof(f218,plain,(
% 1.55/0.61    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(superposition,[],[f86,f84])).
% 1.55/0.61  fof(f86,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(definition_unfolding,[],[f74,f65])).
% 1.55/0.61  fof(f74,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f1])).
% 1.55/0.61  fof(f1,axiom,(
% 1.55/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.55/0.61  fof(f68,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f31])).
% 1.55/0.61  fof(f246,plain,(
% 1.55/0.61    spl6_28 | ~spl6_27),
% 1.55/0.61    inference(avatar_split_clause,[],[f241,f236,f243])).
% 1.55/0.61  fof(f241,plain,(
% 1.55/0.61    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_27),
% 1.55/0.61    inference(resolution,[],[f238,f85])).
% 1.55/0.61  fof(f85,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.55/0.61    inference(definition_unfolding,[],[f75,f65])).
% 1.55/0.61  fof(f75,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f1])).
% 1.55/0.61  fof(f239,plain,(
% 1.55/0.61    spl6_4 | spl6_27 | spl6_7 | ~spl6_5),
% 1.55/0.61    inference(avatar_split_clause,[],[f232,f115,f125,f236,f110])).
% 1.55/0.61  % (25874)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.55/0.61  fof(f115,plain,(
% 1.55/0.61    spl6_5 <=> r1_subset_1(sK2,sK3)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.55/0.61  fof(f232,plain,(
% 1.55/0.61    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_5),
% 1.55/0.61    inference(resolution,[],[f71,f117])).
% 1.55/0.61  fof(f117,plain,(
% 1.55/0.61    r1_subset_1(sK2,sK3) | ~spl6_5),
% 1.55/0.61    inference(avatar_component_clause,[],[f115])).
% 1.55/0.61  fof(f71,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f33])).
% 1.55/0.61  fof(f33,plain,(
% 1.55/0.61    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.55/0.61    inference(flattening,[],[f32])).
% 1.55/0.61  fof(f32,plain,(
% 1.55/0.61    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.55/0.61    inference(ennf_transformation,[],[f11])).
% 1.55/0.61  fof(f11,axiom,(
% 1.55/0.61    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.55/0.61  fof(f217,plain,(
% 1.55/0.61    spl6_24 | ~spl6_11),
% 1.55/0.61    inference(avatar_split_clause,[],[f207,f145,f214])).
% 1.55/0.61  fof(f207,plain,(
% 1.55/0.61    v4_relat_1(sK5,sK3) | ~spl6_11),
% 1.55/0.61    inference(resolution,[],[f79,f147])).
% 1.55/0.61  fof(f79,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f39])).
% 1.55/0.61  fof(f39,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(ennf_transformation,[],[f21])).
% 1.55/0.61  fof(f21,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.55/0.61    inference(pure_predicate_removal,[],[f13])).
% 1.55/0.61  fof(f13,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.55/0.61  fof(f212,plain,(
% 1.55/0.61    spl6_23 | ~spl6_8),
% 1.55/0.61    inference(avatar_split_clause,[],[f206,f130,f209])).
% 1.55/0.61  fof(f206,plain,(
% 1.55/0.61    v4_relat_1(sK4,sK2) | ~spl6_8),
% 1.55/0.61    inference(resolution,[],[f79,f132])).
% 1.55/0.61  fof(f205,plain,(
% 1.55/0.61    spl6_22 | ~spl6_11),
% 1.55/0.61    inference(avatar_split_clause,[],[f195,f145,f202])).
% 1.55/0.61  fof(f195,plain,(
% 1.55/0.61    v1_relat_1(sK5) | ~spl6_11),
% 1.55/0.61    inference(resolution,[],[f78,f147])).
% 1.55/0.61  fof(f78,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f38])).
% 1.55/0.61  fof(f38,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(ennf_transformation,[],[f12])).
% 1.55/0.61  fof(f12,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.55/0.61  fof(f200,plain,(
% 1.55/0.61    spl6_21 | ~spl6_8),
% 1.55/0.61    inference(avatar_split_clause,[],[f194,f130,f197])).
% 1.55/0.61  fof(f194,plain,(
% 1.55/0.61    v1_relat_1(sK4) | ~spl6_8),
% 1.55/0.61    inference(resolution,[],[f78,f132])).
% 1.55/0.61  fof(f171,plain,(
% 1.55/0.61    ~spl6_14 | ~spl6_15 | ~spl6_16),
% 1.55/0.61    inference(avatar_split_clause,[],[f44,f168,f164,f160])).
% 1.55/0.61  fof(f44,plain,(
% 1.55/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f23,plain,(
% 1.55/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.55/0.61    inference(flattening,[],[f22])).
% 1.55/0.61  fof(f22,plain,(
% 1.55/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.55/0.61    inference(ennf_transformation,[],[f20])).
% 1.55/0.61  fof(f20,negated_conjecture,(
% 1.55/0.61    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.55/0.61    inference(negated_conjecture,[],[f19])).
% 1.55/0.61  fof(f19,conjecture,(
% 1.55/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.55/0.61  fof(f158,plain,(
% 1.55/0.61    spl6_13),
% 1.55/0.61    inference(avatar_split_clause,[],[f45,f155])).
% 1.55/0.61  fof(f45,plain,(
% 1.55/0.61    v1_funct_1(sK5)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f153,plain,(
% 1.55/0.61    spl6_12),
% 1.55/0.61    inference(avatar_split_clause,[],[f46,f150])).
% 1.55/0.61  fof(f46,plain,(
% 1.55/0.61    v1_funct_2(sK5,sK3,sK1)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f148,plain,(
% 1.55/0.61    spl6_11),
% 1.55/0.61    inference(avatar_split_clause,[],[f47,f145])).
% 1.55/0.61  fof(f47,plain,(
% 1.55/0.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f143,plain,(
% 1.55/0.61    spl6_10),
% 1.55/0.61    inference(avatar_split_clause,[],[f48,f140])).
% 1.55/0.61  fof(f48,plain,(
% 1.55/0.61    v1_funct_1(sK4)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f138,plain,(
% 1.55/0.61    spl6_9),
% 1.55/0.61    inference(avatar_split_clause,[],[f49,f135])).
% 1.55/0.61  fof(f49,plain,(
% 1.55/0.61    v1_funct_2(sK4,sK2,sK1)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f133,plain,(
% 1.55/0.61    spl6_8),
% 1.55/0.61    inference(avatar_split_clause,[],[f50,f130])).
% 1.55/0.61  fof(f50,plain,(
% 1.55/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f128,plain,(
% 1.55/0.61    ~spl6_7),
% 1.55/0.61    inference(avatar_split_clause,[],[f51,f125])).
% 1.55/0.61  fof(f51,plain,(
% 1.55/0.61    ~v1_xboole_0(sK3)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f123,plain,(
% 1.55/0.61    spl6_6),
% 1.55/0.61    inference(avatar_split_clause,[],[f52,f120])).
% 1.55/0.61  fof(f52,plain,(
% 1.55/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f118,plain,(
% 1.55/0.61    spl6_5),
% 1.55/0.61    inference(avatar_split_clause,[],[f53,f115])).
% 1.55/0.61  fof(f53,plain,(
% 1.55/0.61    r1_subset_1(sK2,sK3)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f113,plain,(
% 1.55/0.61    ~spl6_4),
% 1.55/0.61    inference(avatar_split_clause,[],[f54,f110])).
% 1.55/0.61  fof(f54,plain,(
% 1.55/0.61    ~v1_xboole_0(sK2)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f108,plain,(
% 1.55/0.61    spl6_3),
% 1.55/0.61    inference(avatar_split_clause,[],[f55,f105])).
% 1.55/0.61  fof(f55,plain,(
% 1.55/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f103,plain,(
% 1.55/0.61    ~spl6_2),
% 1.55/0.61    inference(avatar_split_clause,[],[f56,f100])).
% 1.55/0.61  fof(f56,plain,(
% 1.55/0.61    ~v1_xboole_0(sK1)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  fof(f98,plain,(
% 1.55/0.61    ~spl6_1),
% 1.55/0.61    inference(avatar_split_clause,[],[f57,f95])).
% 1.55/0.61  fof(f57,plain,(
% 1.55/0.61    ~v1_xboole_0(sK0)),
% 1.55/0.61    inference(cnf_transformation,[],[f23])).
% 1.55/0.61  % SZS output end Proof for theBenchmark
% 1.55/0.61  % (25860)------------------------------
% 1.55/0.61  % (25860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (25860)Termination reason: Refutation
% 1.55/0.61  
% 1.55/0.61  % (25860)Memory used [KB]: 11641
% 1.55/0.61  % (25860)Time elapsed: 0.183 s
% 1.55/0.61  % (25860)------------------------------
% 1.55/0.61  % (25860)------------------------------
% 1.55/0.61  % (25843)Success in time 0.252 s
%------------------------------------------------------------------------------
