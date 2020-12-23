%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:30 EST 2020

% Result     : Theorem 2.46s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  269 ( 663 expanded)
%              Number of leaves         :   62 ( 311 expanded)
%              Depth                    :   14
%              Number of atoms          : 1389 (3108 expanded)
%              Number of equality atoms :  169 ( 482 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1555,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f168,f197,f202,f209,f214,f271,f276,f448,f449,f450,f455,f465,f468,f489,f545,f556,f558,f568,f571,f575,f621,f661,f696,f739,f779,f878,f970,f1132,f1278,f1282,f1312,f1313,f1548])).

fof(f1548,plain,
    ( ~ spl7_36
    | ~ spl7_47
    | spl7_70 ),
    inference(avatar_contradiction_clause,[],[f1547])).

fof(f1547,plain,
    ( $false
    | ~ spl7_36
    | ~ spl7_47
    | spl7_70 ),
    inference(trivial_inequality_removal,[],[f1543])).

fof(f1543,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_36
    | ~ spl7_47
    | spl7_70 ),
    inference(superposition,[],[f583,f1536])).

% (21352)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f1536,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(sK4,X0)
    | ~ spl7_36
    | ~ spl7_47 ),
    inference(resolution,[],[f383,f217])).

fof(f217,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f83,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f65])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f383,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_36
    | ~ spl7_47 ),
    inference(backward_demodulation,[],[f303,f363])).

fof(f363,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl7_47
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl7_36
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f583,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl7_70 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl7_70
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f1313,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_94
    | ~ spl7_90
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
    | ~ spl7_76
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1185,f1129,f486,f290,f286,f199,f194,f117,f658,f97,f107,f102,f122,f117,f137,f132,f127,f152,f147,f142,f875,f967,f92,f161])).

fof(f161,plain,
    ( spl7_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f92,plain,
    ( spl7_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f967,plain,
    ( spl7_94
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f875,plain,
    ( spl7_90
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f142,plain,
    ( spl7_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f147,plain,
    ( spl7_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f152,plain,
    ( spl7_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f127,plain,
    ( spl7_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f132,plain,
    ( spl7_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f137,plain,
    ( spl7_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f122,plain,
    ( spl7_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f102,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f107,plain,
    ( spl7_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f97,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f658,plain,
    ( spl7_76
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f117,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f194,plain,
    ( spl7_21
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f199,plain,
    ( spl7_22
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f286,plain,
    ( spl7_33
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f290,plain,
    ( spl7_34
  <=> ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f486,plain,
    ( spl7_62
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1129,plain,
    ( spl7_116
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f1185,plain,
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
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1184,f255])).

fof(f255,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK4,X0),X1) = k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl7_21 ),
    inference(resolution,[],[f84,f196])).

fof(f196,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f194])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1184,plain,
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
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1183,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f1183,plain,
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
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1182,f488])).

fof(f488,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f486])).

fof(f1182,plain,
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
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1181,f256])).

fof(f256,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK5,X2),X3) = k7_relat_1(sK5,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ spl7_22 ),
    inference(resolution,[],[f84,f201])).

fof(f201,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1181,plain,
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
    | ~ spl7_6
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1180,f287])).

fof(f287,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f286])).

fof(f1180,plain,
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
    | ~ spl7_6
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1179,f252])).

fof(f252,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f85,f119])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f74,f65])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1162,f291])).

fof(f291,plain,
    ( ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f290])).

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
    | ~ spl7_116 ),
    inference(resolution,[],[f1131,f89])).

fof(f89,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f1131,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f1129])).

fof(f1312,plain,
    ( spl7_14
    | spl7_1
    | ~ spl7_94
    | ~ spl7_90
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
    | ~ spl7_76
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1195,f1129,f486,f290,f286,f199,f194,f117,f658,f97,f107,f102,f122,f117,f137,f132,f127,f152,f147,f142,f875,f967,f92,f157])).

fof(f157,plain,
    ( spl7_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f1195,plain,
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
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1194,f255])).

fof(f1194,plain,
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
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1193,f58])).

fof(f1193,plain,
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
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1192,f488])).

fof(f1192,plain,
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
    | ~ spl7_6
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1191,f256])).

fof(f1191,plain,
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
    | ~ spl7_6
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1190,f287])).

fof(f1190,plain,
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
    | ~ spl7_6
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1189,f252])).

fof(f1189,plain,
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
    | ~ spl7_34
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f1163,f291])).

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
    | ~ spl7_116 ),
    inference(resolution,[],[f1131,f88])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f1282,plain,
    ( spl7_48
    | spl7_47
    | ~ spl7_21
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f1281,f279,f194,f361,f365])).

fof(f365,plain,
    ( spl7_48
  <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f279,plain,
    ( spl7_32
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f1281,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | ~ spl7_21
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f672,f281])).

fof(f281,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f672,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl7_21
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f670,f281])).

fof(f670,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(k1_relat_1(sK4)))
    | k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl7_21 ),
    inference(resolution,[],[f244,f196])).

fof(f244,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,sK6(k1_relat_1(X0)))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f62,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r1_xboole_0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f1278,plain,
    ( ~ spl7_70
    | ~ spl7_6
    | spl7_16
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f1277,f486,f290,f286,f240,f199,f165,f117,f582])).

fof(f165,plain,
    ( spl7_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f240,plain,
    ( spl7_28
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f1277,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f1276,f242])).

fof(f242,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f240])).

fof(f1276,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f1275,f58])).

fof(f1275,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f1274,f488])).

fof(f1274,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_22
    | ~ spl7_33
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f1273,f256])).

fof(f1273,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_33
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f1272,f287])).

fof(f1272,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f1271,f252])).

fof(f1271,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f167,f291])).

fof(f167,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f1132,plain,
    ( spl7_116
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f1127,f777,f127,f132,f137,f1129])).

fof(f777,plain,
    ( spl7_86
  <=> ! [X2] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X2,sK2,sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f1127,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_8
    | ~ spl7_86 ),
    inference(resolution,[],[f778,f129])).

fof(f129,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f778,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X2,sK2,sK1)
        | ~ v1_funct_1(X2)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f777])).

fof(f970,plain,
    ( spl7_94
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f965,f737,f127,f132,f137,f967])).

fof(f737,plain,
    ( spl7_82
  <=> ! [X2] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X2,sK2,sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f965,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl7_8
    | ~ spl7_82 ),
    inference(resolution,[],[f738,f129])).

fof(f738,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X2,sK2,sK1)
        | ~ v1_funct_1(X2)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f737])).

fof(f878,plain,
    ( spl7_90
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f873,f694,f127,f132,f137,f875])).

fof(f694,plain,
    ( spl7_78
  <=> ! [X2] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5))
        | ~ v1_funct_2(X2,sK2,sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f873,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_8
    | ~ spl7_78 ),
    inference(resolution,[],[f695,f129])).

fof(f695,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X2,sK2,sK1)
        | ~ v1_funct_1(X2)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5)) )
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f694])).

fof(f779,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_86
    | ~ spl7_11
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f771,f352,f142,f777,f97,f152,f122,f147,f117])).

fof(f352,plain,
    ( spl7_45
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f771,plain,
    ( ! [X2] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl7_11
    | ~ spl7_45 ),
    inference(resolution,[],[f353,f144])).

fof(f144,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f353,plain,
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
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f352])).

fof(f739,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_82
    | ~ spl7_11
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f731,f330,f142,f737,f97,f152,f122,f147,f117])).

fof(f330,plain,
    ( spl7_41
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f731,plain,
    ( ! [X2] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl7_11
    | ~ spl7_41 ),
    inference(resolution,[],[f331,f144])).

fof(f331,plain,
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
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f330])).

fof(f696,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_78
    | ~ spl7_11
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f688,f310,f142,f694,f97,f152,f122,f147,f117])).

fof(f310,plain,
    ( spl7_37
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f688,plain,
    ( ! [X2] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl7_11
    | ~ spl7_37 ),
    inference(resolution,[],[f311,f144])).

fof(f311,plain,
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
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f310])).

fof(f661,plain,
    ( spl7_76
    | ~ spl7_29
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f656,f582,f261,f658])).

fof(f261,plain,
    ( spl7_29
  <=> k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f656,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl7_29
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f263,f584])).

fof(f584,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f582])).

fof(f263,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f261])).

fof(f621,plain,
    ( spl7_70
    | ~ spl7_21
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f580,f365,f194,f582])).

fof(f580,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_21
    | ~ spl7_48 ),
    inference(forward_demodulation,[],[f579,f58])).

fof(f579,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_21
    | ~ spl7_48 ),
    inference(superposition,[],[f257,f367])).

fof(f367,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f365])).

fof(f257,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_21 ),
    inference(superposition,[],[f255,f81])).

fof(f575,plain,
    ( spl7_29
    | ~ spl7_21
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f572,f240,f194,f261])).

fof(f572,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3)
    | ~ spl7_21
    | ~ spl7_28 ),
    inference(superposition,[],[f255,f242])).

fof(f571,plain,
    ( ~ spl7_22
    | spl7_44
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f569,f295,f344,f199])).

fof(f344,plain,
    ( spl7_44
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f295,plain,
    ( spl7_35
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f569,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_35 ),
    inference(superposition,[],[f62,f297])).

fof(f297,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f295])).

fof(f568,plain,
    ( spl7_34
    | ~ spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f559,f142,f152,f290])).

fof(f559,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f144,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f558,plain,
    ( ~ spl7_22
    | spl7_35
    | ~ spl7_24
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f557,f273,f211,f295,f199])).

fof(f211,plain,
    ( spl7_24
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f273,plain,
    ( spl7_31
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f557,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl7_31 ),
    inference(resolution,[],[f275,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f275,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f273])).

fof(f556,plain,
    ( spl7_28
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f555,f233,f240])).

fof(f233,plain,
    ( spl7_27
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f555,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_27 ),
    inference(resolution,[],[f235,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f235,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f233])).

fof(f545,plain,
    ( spl7_4
    | spl7_27
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f544,f112,f122,f233,f107])).

fof(f112,plain,
    ( spl7_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f544,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f114,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f114,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f489,plain,
    ( spl7_62
    | ~ spl7_27
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f475,f344,f233,f486])).

fof(f475,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_27
    | ~ spl7_44 ),
    inference(resolution,[],[f345,f235])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f344])).

fof(f468,plain,
    ( ~ spl7_21
    | spl7_36
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f466,f279,f302,f194])).

fof(f466,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_32 ),
    inference(superposition,[],[f62,f281])).

fof(f465,plain,
    ( spl7_33
    | ~ spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f456,f127,f137,f286])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f129,f77])).

fof(f455,plain,
    ( ~ spl7_21
    | spl7_32
    | ~ spl7_23
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f454,f268,f206,f279,f194])).

fof(f206,plain,
    ( spl7_23
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f268,plain,
    ( spl7_30
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f454,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl7_30 ),
    inference(resolution,[],[f270,f70])).

fof(f270,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f450,plain,
    ( spl7_1
    | spl7_4
    | spl7_37
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f445,f102,f310,f107,f92])).

fof(f445,plain,
    ( ! [X10,X8,X11,X9] :
        ( v1_xboole_0(X8)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,sK2,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK2,X8)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X8)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X8)))
        | v1_funct_1(k1_tmap_1(sK0,X8,sK2,X9,X10,X11)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f104,f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f42])).

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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f449,plain,
    ( spl7_1
    | spl7_4
    | spl7_41
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f444,f102,f330,f107,f92])).

fof(f444,plain,
    ( ! [X6,X4,X7,X5] :
        ( v1_xboole_0(X4)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK2,X4)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,X5,X4)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
        | v1_funct_2(k1_tmap_1(sK0,X4,sK2,X5,X6,X7),k4_subset_1(sK0,sK2,X5),X4) )
    | ~ spl7_3 ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f448,plain,
    ( spl7_1
    | spl7_4
    | spl7_45
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f443,f102,f352,f107,f92])).

fof(f443,plain,
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
    inference(resolution,[],[f104,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f276,plain,
    ( spl7_31
    | ~ spl7_12
    | ~ spl7_13
    | spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f266,f142,f97,f152,f147,f273])).

fof(f266,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f66,f144])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f271,plain,
    ( spl7_30
    | ~ spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f265,f127,f97,f137,f132,f268])).

fof(f265,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f66,f129])).

fof(f214,plain,
    ( spl7_24
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f204,f142,f211])).

fof(f204,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f76,f144])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f209,plain,
    ( spl7_23
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f203,f127,f206])).

fof(f203,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f76,f129])).

fof(f202,plain,
    ( spl7_22
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f192,f142,f199])).

fof(f192,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_11 ),
    inference(resolution,[],[f75,f144])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f197,plain,
    ( spl7_21
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f191,f127,f194])).

fof(f191,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_8 ),
    inference(resolution,[],[f75,f129])).

fof(f168,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f43,f165,f161,f157])).

fof(f43,plain,
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f155,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f44,f152])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f150,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f45,f147])).

fof(f45,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f145,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f46,f142])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f140,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f47,f137])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f135,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f48,f132])).

fof(f48,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f130,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f49,f127])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f50,f122])).

fof(f50,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f51,f117])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f115,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f52,f112])).

fof(f52,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f110,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f53,f107])).

fof(f53,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f54,f102])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f55,f97])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f56,f92])).

fof(f56,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (21306)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (21303)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (21301)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (21298)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (21327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (21319)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (21304)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (21326)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (21318)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (21316)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (21317)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (21300)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (21320)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (21299)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (21307)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (21310)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (21311)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (21315)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (21325)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (21302)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (21305)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (21324)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.56  % (21309)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.56  % (21322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.56  % (21297)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.56  % (21315)Refutation not found, incomplete strategy% (21315)------------------------------
% 1.38/0.56  % (21315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (21321)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.56  % (21315)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (21315)Memory used [KB]: 10746
% 1.38/0.56  % (21315)Time elapsed: 0.149 s
% 1.38/0.56  % (21315)------------------------------
% 1.38/0.56  % (21315)------------------------------
% 1.38/0.57  % (21313)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.57  % (21308)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.67/0.59  % (21323)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.67/0.59  % (21320)Refutation not found, incomplete strategy% (21320)------------------------------
% 1.67/0.59  % (21320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (21320)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.59  
% 1.67/0.59  % (21320)Memory used [KB]: 11513
% 1.67/0.59  % (21320)Time elapsed: 0.128 s
% 1.67/0.59  % (21320)------------------------------
% 1.67/0.59  % (21320)------------------------------
% 1.67/0.60  % (21314)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.67/0.64  % (21307)Refutation not found, incomplete strategy% (21307)------------------------------
% 1.67/0.64  % (21307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.65  % (21307)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.65  
% 1.67/0.65  % (21307)Memory used [KB]: 11513
% 1.67/0.65  % (21307)Time elapsed: 0.201 s
% 1.67/0.65  % (21307)------------------------------
% 1.67/0.65  % (21307)------------------------------
% 2.46/0.71  % (21314)Refutation found. Thanks to Tanya!
% 2.46/0.71  % SZS status Theorem for theBenchmark
% 2.73/0.72  % SZS output start Proof for theBenchmark
% 2.73/0.72  fof(f1555,plain,(
% 2.73/0.72    $false),
% 2.73/0.72    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f168,f197,f202,f209,f214,f271,f276,f448,f449,f450,f455,f465,f468,f489,f545,f556,f558,f568,f571,f575,f621,f661,f696,f739,f779,f878,f970,f1132,f1278,f1282,f1312,f1313,f1548])).
% 2.73/0.72  fof(f1548,plain,(
% 2.73/0.72    ~spl7_36 | ~spl7_47 | spl7_70),
% 2.73/0.72    inference(avatar_contradiction_clause,[],[f1547])).
% 2.73/0.72  fof(f1547,plain,(
% 2.73/0.72    $false | (~spl7_36 | ~spl7_47 | spl7_70)),
% 2.73/0.72    inference(trivial_inequality_removal,[],[f1543])).
% 2.73/0.72  fof(f1543,plain,(
% 2.73/0.72    k1_xboole_0 != k1_xboole_0 | (~spl7_36 | ~spl7_47 | spl7_70)),
% 2.73/0.72    inference(superposition,[],[f583,f1536])).
% 2.73/0.72  % (21352)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.73/0.73  fof(f1536,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK4,X0)) ) | (~spl7_36 | ~spl7_47)),
% 2.73/0.73    inference(resolution,[],[f383,f217])).
% 2.73/0.73  fof(f217,plain,(
% 2.73/0.73    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.73/0.73    inference(trivial_inequality_removal,[],[f216])).
% 2.73/0.73  fof(f216,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 2.73/0.73    inference(superposition,[],[f83,f81])).
% 2.73/0.73  fof(f81,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f57,f65])).
% 2.73/0.73  fof(f65,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.73/0.73    inference(cnf_transformation,[],[f5])).
% 2.73/0.73  fof(f5,axiom,(
% 2.73/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.73/0.73  fof(f57,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f2])).
% 2.73/0.73  fof(f2,axiom,(
% 2.73/0.73    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.73/0.73  fof(f83,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.73/0.73    inference(definition_unfolding,[],[f71,f65])).
% 2.73/0.73  fof(f71,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f1])).
% 2.73/0.73  fof(f1,axiom,(
% 2.73/0.73    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.73/0.73  fof(f383,plain,(
% 2.73/0.73    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | (~spl7_36 | ~spl7_47)),
% 2.73/0.73    inference(backward_demodulation,[],[f303,f363])).
% 2.73/0.73  fof(f363,plain,(
% 2.73/0.73    k1_xboole_0 = sK2 | ~spl7_47),
% 2.73/0.73    inference(avatar_component_clause,[],[f361])).
% 2.73/0.73  fof(f361,plain,(
% 2.73/0.73    spl7_47 <=> k1_xboole_0 = sK2),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.73/0.73  fof(f303,plain,(
% 2.73/0.73    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_36),
% 2.73/0.73    inference(avatar_component_clause,[],[f302])).
% 2.73/0.73  fof(f302,plain,(
% 2.73/0.73    spl7_36 <=> ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.73/0.73  fof(f583,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl7_70),
% 2.73/0.73    inference(avatar_component_clause,[],[f582])).
% 2.73/0.73  fof(f582,plain,(
% 2.73/0.73    spl7_70 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 2.73/0.73  fof(f1313,plain,(
% 2.73/0.73    spl7_15 | spl7_1 | ~spl7_94 | ~spl7_90 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_76 | ~spl7_6 | ~spl7_21 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116),
% 2.73/0.73    inference(avatar_split_clause,[],[f1185,f1129,f486,f290,f286,f199,f194,f117,f658,f97,f107,f102,f122,f117,f137,f132,f127,f152,f147,f142,f875,f967,f92,f161])).
% 2.73/0.73  fof(f161,plain,(
% 2.73/0.73    spl7_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.73/0.73  fof(f92,plain,(
% 2.73/0.73    spl7_1 <=> v1_xboole_0(sK0)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.73/0.73  fof(f967,plain,(
% 2.73/0.73    spl7_94 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).
% 2.73/0.73  fof(f875,plain,(
% 2.73/0.73    spl7_90 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 2.73/0.73  fof(f142,plain,(
% 2.73/0.73    spl7_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.73/0.73  fof(f147,plain,(
% 2.73/0.73    spl7_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.73/0.73  fof(f152,plain,(
% 2.73/0.73    spl7_13 <=> v1_funct_1(sK5)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.73/0.73  fof(f127,plain,(
% 2.73/0.73    spl7_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.73/0.73  fof(f132,plain,(
% 2.73/0.73    spl7_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.73/0.73  fof(f137,plain,(
% 2.73/0.73    spl7_10 <=> v1_funct_1(sK4)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.73/0.73  fof(f122,plain,(
% 2.73/0.73    spl7_7 <=> v1_xboole_0(sK3)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.73/0.73  fof(f102,plain,(
% 2.73/0.73    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.73/0.73  fof(f107,plain,(
% 2.73/0.73    spl7_4 <=> v1_xboole_0(sK2)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.73/0.73  fof(f97,plain,(
% 2.73/0.73    spl7_2 <=> v1_xboole_0(sK1)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.73/0.73  fof(f658,plain,(
% 2.73/0.73    spl7_76 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 2.73/0.73  fof(f117,plain,(
% 2.73/0.73    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.73/0.73  fof(f194,plain,(
% 2.73/0.73    spl7_21 <=> v1_relat_1(sK4)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.73/0.73  fof(f199,plain,(
% 2.73/0.73    spl7_22 <=> v1_relat_1(sK5)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.73/0.73  fof(f286,plain,(
% 2.73/0.73    spl7_33 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 2.73/0.73  fof(f290,plain,(
% 2.73/0.73    spl7_34 <=> ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.73/0.73  fof(f486,plain,(
% 2.73/0.73    spl7_62 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 2.73/0.73  fof(f1129,plain,(
% 2.73/0.73    spl7_116 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).
% 2.73/0.73  fof(f1185,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(k7_relat_1(sK4,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_21 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1184,f255])).
% 2.73/0.73  fof(f255,plain,(
% 2.73/0.73    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK4,X0),X1) = k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl7_21),
% 2.73/0.73    inference(resolution,[],[f84,f196])).
% 2.73/0.73  fof(f196,plain,(
% 2.73/0.73    v1_relat_1(sK4) | ~spl7_21),
% 2.73/0.73    inference(avatar_component_clause,[],[f194])).
% 2.73/0.73  fof(f84,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f73,f65])).
% 2.73/0.73  fof(f73,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 2.73/0.73    inference(cnf_transformation,[],[f35])).
% 2.73/0.73  fof(f35,plain,(
% 2.73/0.73    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.73/0.73    inference(ennf_transformation,[],[f6])).
% 2.73/0.73  fof(f6,axiom,(
% 2.73/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 2.73/0.73  fof(f1184,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1183,f58])).
% 2.73/0.73  fof(f58,plain,(
% 2.73/0.73    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f7])).
% 2.73/0.73  fof(f7,axiom,(
% 2.73/0.73    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 2.73/0.73  fof(f1183,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1182,f488])).
% 2.73/0.73  fof(f488,plain,(
% 2.73/0.73    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl7_62),
% 2.73/0.73    inference(avatar_component_clause,[],[f486])).
% 2.73/0.73  fof(f1182,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1181,f256])).
% 2.73/0.73  fof(f256,plain,(
% 2.73/0.73    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK5,X2),X3) = k7_relat_1(sK5,k1_setfam_1(k2_tarski(X2,X3)))) ) | ~spl7_22),
% 2.73/0.73    inference(resolution,[],[f84,f201])).
% 2.73/0.73  fof(f201,plain,(
% 2.73/0.73    v1_relat_1(sK5) | ~spl7_22),
% 2.73/0.73    inference(avatar_component_clause,[],[f199])).
% 2.73/0.73  fof(f1181,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_33 | ~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1180,f287])).
% 2.73/0.73  fof(f287,plain,(
% 2.73/0.73    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_33),
% 2.73/0.73    inference(avatar_component_clause,[],[f286])).
% 2.73/0.73  fof(f1180,plain,(
% 2.73/0.73    k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1179,f252])).
% 2.73/0.73  fof(f252,plain,(
% 2.73/0.73    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl7_6),
% 2.73/0.73    inference(resolution,[],[f85,f119])).
% 2.73/0.73  fof(f119,plain,(
% 2.73/0.73    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_6),
% 2.73/0.73    inference(avatar_component_clause,[],[f117])).
% 2.73/0.73  fof(f85,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.73/0.73    inference(definition_unfolding,[],[f74,f65])).
% 2.73/0.73  fof(f74,plain,(
% 2.73/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f36])).
% 2.73/0.73  fof(f36,plain,(
% 2.73/0.73    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.73/0.73    inference(ennf_transformation,[],[f3])).
% 2.73/0.73  fof(f3,axiom,(
% 2.73/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.73/0.73  fof(f1179,plain,(
% 2.73/0.73    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1162,f291])).
% 2.73/0.73  fof(f291,plain,(
% 2.73/0.73    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) ) | ~spl7_34),
% 2.73/0.73    inference(avatar_component_clause,[],[f290])).
% 2.73/0.73  fof(f1162,plain,(
% 2.73/0.73    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl7_116),
% 2.73/0.73    inference(resolution,[],[f1131,f89])).
% 2.73/0.73  fof(f89,plain,(
% 2.73/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 2.73/0.73    inference(equality_resolution,[],[f59])).
% 2.73/0.73  fof(f59,plain,(
% 2.73/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.73/0.73    inference(cnf_transformation,[],[f25])).
% 2.73/0.73  fof(f25,plain,(
% 2.73/0.73    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.73/0.73    inference(flattening,[],[f24])).
% 2.73/0.73  fof(f24,plain,(
% 2.73/0.73    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f16])).
% 2.73/0.73  fof(f16,axiom,(
% 2.73/0.73    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.73/0.73  fof(f1131,plain,(
% 2.73/0.73    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl7_116),
% 2.73/0.73    inference(avatar_component_clause,[],[f1129])).
% 2.73/0.73  fof(f1312,plain,(
% 2.73/0.73    spl7_14 | spl7_1 | ~spl7_94 | ~spl7_90 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_76 | ~spl7_6 | ~spl7_21 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116),
% 2.73/0.73    inference(avatar_split_clause,[],[f1195,f1129,f486,f290,f286,f199,f194,f117,f658,f97,f107,f102,f122,f117,f137,f132,f127,f152,f147,f142,f875,f967,f92,f157])).
% 2.73/0.73  fof(f157,plain,(
% 2.73/0.73    spl7_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.73/0.73  fof(f1195,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(k7_relat_1(sK4,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_21 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1194,f255])).
% 2.73/0.73  fof(f1194,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1193,f58])).
% 2.73/0.73  fof(f1193,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1192,f488])).
% 2.73/0.73  fof(f1192,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1191,f256])).
% 2.73/0.73  fof(f1191,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_33 | ~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1190,f287])).
% 2.73/0.73  fof(f1190,plain,(
% 2.73/0.73    k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1189,f252])).
% 2.73/0.73  fof(f1189,plain,(
% 2.73/0.73    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_34 | ~spl7_116)),
% 2.73/0.73    inference(forward_demodulation,[],[f1163,f291])).
% 2.73/0.73  fof(f1163,plain,(
% 2.73/0.73    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl7_116),
% 2.73/0.73    inference(resolution,[],[f1131,f88])).
% 2.73/0.73  fof(f88,plain,(
% 2.73/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 2.73/0.73    inference(equality_resolution,[],[f60])).
% 2.73/0.73  fof(f60,plain,(
% 2.73/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.73/0.73    inference(cnf_transformation,[],[f25])).
% 2.73/0.73  fof(f1282,plain,(
% 2.73/0.73    spl7_48 | spl7_47 | ~spl7_21 | ~spl7_32),
% 2.73/0.73    inference(avatar_split_clause,[],[f1281,f279,f194,f361,f365])).
% 2.73/0.73  fof(f365,plain,(
% 2.73/0.73    spl7_48 <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 2.73/0.73  fof(f279,plain,(
% 2.73/0.73    spl7_32 <=> sK2 = k1_relat_1(sK4)),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 2.73/0.73  fof(f1281,plain,(
% 2.73/0.73    k1_xboole_0 = sK2 | k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | (~spl7_21 | ~spl7_32)),
% 2.73/0.73    inference(forward_demodulation,[],[f672,f281])).
% 2.73/0.73  fof(f281,plain,(
% 2.73/0.73    sK2 = k1_relat_1(sK4) | ~spl7_32),
% 2.73/0.73    inference(avatar_component_clause,[],[f279])).
% 2.73/0.73  fof(f672,plain,(
% 2.73/0.73    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | k1_xboole_0 = k1_relat_1(sK4) | (~spl7_21 | ~spl7_32)),
% 2.73/0.73    inference(forward_demodulation,[],[f670,f281])).
% 2.73/0.73  fof(f670,plain,(
% 2.73/0.73    k1_xboole_0 = k7_relat_1(sK4,sK6(k1_relat_1(sK4))) | k1_xboole_0 = k1_relat_1(sK4) | ~spl7_21),
% 2.73/0.73    inference(resolution,[],[f244,f196])).
% 2.73/0.73  fof(f244,plain,(
% 2.73/0.73    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,sK6(k1_relat_1(X0))) | k1_xboole_0 = k1_relat_1(X0)) )),
% 2.73/0.73    inference(resolution,[],[f62,f64])).
% 2.73/0.73  fof(f64,plain,(
% 2.73/0.73    ( ! [X0] : (r1_xboole_0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.73/0.73    inference(cnf_transformation,[],[f28])).
% 2.73/0.73  fof(f28,plain,(
% 2.73/0.73    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 2.73/0.73    inference(ennf_transformation,[],[f20])).
% 2.73/0.73  fof(f20,plain,(
% 2.73/0.73    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 2.73/0.73    inference(pure_predicate_removal,[],[f12])).
% 2.73/0.73  fof(f12,axiom,(
% 2.73/0.73    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 2.73/0.73  fof(f62,plain,(
% 2.73/0.73    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 2.73/0.73    inference(cnf_transformation,[],[f26])).
% 2.73/0.73  fof(f26,plain,(
% 2.73/0.73    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.73/0.73    inference(ennf_transformation,[],[f8])).
% 2.73/0.73  fof(f8,axiom,(
% 2.73/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.73/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 2.73/0.73  fof(f1278,plain,(
% 2.73/0.73    ~spl7_70 | ~spl7_6 | spl7_16 | ~spl7_22 | ~spl7_28 | ~spl7_33 | ~spl7_34 | ~spl7_62),
% 2.73/0.73    inference(avatar_split_clause,[],[f1277,f486,f290,f286,f240,f199,f165,f117,f582])).
% 2.73/0.73  fof(f165,plain,(
% 2.73/0.73    spl7_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.73/0.73  fof(f240,plain,(
% 2.73/0.73    spl7_28 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.73/0.73  fof(f1277,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_22 | ~spl7_28 | ~spl7_33 | ~spl7_34 | ~spl7_62)),
% 2.73/0.73    inference(forward_demodulation,[],[f1276,f242])).
% 2.73/0.73  fof(f242,plain,(
% 2.73/0.73    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_28),
% 2.73/0.73    inference(avatar_component_clause,[],[f240])).
% 2.73/0.73  fof(f1276,plain,(
% 2.73/0.73    k1_xboole_0 != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62)),
% 2.73/0.73    inference(forward_demodulation,[],[f1275,f58])).
% 2.73/0.73  fof(f1275,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k1_xboole_0,sK3) | (~spl7_6 | spl7_16 | ~spl7_22 | ~spl7_33 | ~spl7_34 | ~spl7_62)),
% 2.73/0.73    inference(forward_demodulation,[],[f1274,f488])).
% 2.73/0.73  fof(f1274,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(k7_relat_1(sK5,sK2),sK3) | (~spl7_6 | spl7_16 | ~spl7_22 | ~spl7_33 | ~spl7_34)),
% 2.73/0.73    inference(forward_demodulation,[],[f1273,f256])).
% 2.73/0.73  fof(f1273,plain,(
% 2.73/0.73    k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_33 | ~spl7_34)),
% 2.73/0.73    inference(forward_demodulation,[],[f1272,f287])).
% 2.73/0.73  fof(f1272,plain,(
% 2.73/0.73    k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_34)),
% 2.73/0.73    inference(forward_demodulation,[],[f1271,f252])).
% 2.73/0.73  fof(f1271,plain,(
% 2.73/0.73    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_16 | ~spl7_34)),
% 2.73/0.73    inference(forward_demodulation,[],[f167,f291])).
% 2.73/0.73  fof(f167,plain,(
% 2.73/0.73    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_16),
% 2.73/0.73    inference(avatar_component_clause,[],[f165])).
% 2.73/0.73  fof(f1132,plain,(
% 2.73/0.73    spl7_116 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_86),
% 2.73/0.73    inference(avatar_split_clause,[],[f1127,f777,f127,f132,f137,f1129])).
% 2.73/0.73  fof(f777,plain,(
% 2.73/0.73    spl7_86 <=> ! [X2] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X2,sK2,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).
% 2.73/0.73  fof(f1127,plain,(
% 2.73/0.73    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl7_8 | ~spl7_86)),
% 2.73/0.73    inference(resolution,[],[f778,f129])).
% 2.73/0.73  fof(f129,plain,(
% 2.73/0.73    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_8),
% 2.73/0.73    inference(avatar_component_clause,[],[f127])).
% 2.73/0.73  fof(f778,plain,(
% 2.73/0.73    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X2,sK2,sK1) | ~v1_funct_1(X2) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl7_86),
% 2.73/0.73    inference(avatar_component_clause,[],[f777])).
% 2.73/0.73  fof(f970,plain,(
% 2.73/0.73    spl7_94 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_82),
% 2.73/0.73    inference(avatar_split_clause,[],[f965,f737,f127,f132,f137,f967])).
% 2.73/0.73  fof(f737,plain,(
% 2.73/0.73    spl7_82 <=> ! [X2] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X2,sK2,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 2.73/0.73  fof(f965,plain,(
% 2.73/0.73    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl7_8 | ~spl7_82)),
% 2.73/0.73    inference(resolution,[],[f738,f129])).
% 2.73/0.73  fof(f738,plain,(
% 2.73/0.73    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X2,sK2,sK1) | ~v1_funct_1(X2) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl7_82),
% 2.73/0.73    inference(avatar_component_clause,[],[f737])).
% 2.73/0.73  fof(f878,plain,(
% 2.73/0.73    spl7_90 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_78),
% 2.73/0.73    inference(avatar_split_clause,[],[f873,f694,f127,f132,f137,f875])).
% 2.73/0.73  fof(f694,plain,(
% 2.73/0.73    spl7_78 <=> ! [X2] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5)) | ~v1_funct_2(X2,sK2,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 2.73/0.73  fof(f873,plain,(
% 2.73/0.73    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl7_8 | ~spl7_78)),
% 2.73/0.73    inference(resolution,[],[f695,f129])).
% 2.73/0.73  fof(f695,plain,(
% 2.73/0.73    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X2,sK2,sK1) | ~v1_funct_1(X2) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5))) ) | ~spl7_78),
% 2.73/0.73    inference(avatar_component_clause,[],[f694])).
% 2.73/0.73  fof(f779,plain,(
% 2.73/0.73    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_86 | ~spl7_11 | ~spl7_45),
% 2.73/0.73    inference(avatar_split_clause,[],[f771,f352,f142,f777,f97,f152,f122,f147,f117])).
% 2.73/0.73  fof(f352,plain,(
% 2.73/0.73    spl7_45 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.73/0.73    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.73/0.73  fof(f771,plain,(
% 2.73/0.73    ( ! [X2] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_45)),
% 2.73/0.73    inference(resolution,[],[f353,f144])).
% 2.73/0.73  fof(f144,plain,(
% 2.73/0.73    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_11),
% 2.73/0.73    inference(avatar_component_clause,[],[f142])).
% 2.73/0.73  fof(f353,plain,(
% 2.73/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_45),
% 2.73/0.73    inference(avatar_component_clause,[],[f352])).
% 2.82/0.74  fof(f739,plain,(
% 2.82/0.74    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_82 | ~spl7_11 | ~spl7_41),
% 2.82/0.74    inference(avatar_split_clause,[],[f731,f330,f142,f737,f97,f152,f122,f147,f117])).
% 2.82/0.74  fof(f330,plain,(
% 2.82/0.74    spl7_41 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 2.82/0.74  fof(f731,plain,(
% 2.82/0.74    ( ! [X2] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_41)),
% 2.82/0.74    inference(resolution,[],[f331,f144])).
% 2.82/0.74  fof(f331,plain,(
% 2.82/0.74    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_41),
% 2.82/0.74    inference(avatar_component_clause,[],[f330])).
% 2.82/0.74  fof(f696,plain,(
% 2.82/0.74    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_78 | ~spl7_11 | ~spl7_37),
% 2.82/0.74    inference(avatar_split_clause,[],[f688,f310,f142,f694,f97,f152,f122,f147,f117])).
% 2.82/0.74  fof(f310,plain,(
% 2.82/0.74    spl7_37 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 2.82/0.74  fof(f688,plain,(
% 2.82/0.74    ( ! [X2] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X2,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_37)),
% 2.82/0.74    inference(resolution,[],[f311,f144])).
% 2.82/0.74  fof(f311,plain,(
% 2.82/0.74    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_37),
% 2.82/0.74    inference(avatar_component_clause,[],[f310])).
% 2.82/0.74  fof(f661,plain,(
% 2.82/0.74    spl7_76 | ~spl7_29 | ~spl7_70),
% 2.82/0.74    inference(avatar_split_clause,[],[f656,f582,f261,f658])).
% 2.82/0.74  fof(f261,plain,(
% 2.82/0.74    spl7_29 <=> k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 2.82/0.74  fof(f656,plain,(
% 2.82/0.74    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | (~spl7_29 | ~spl7_70)),
% 2.82/0.74    inference(forward_demodulation,[],[f263,f584])).
% 2.82/0.74  fof(f584,plain,(
% 2.82/0.74    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_70),
% 2.82/0.74    inference(avatar_component_clause,[],[f582])).
% 2.82/0.74  fof(f263,plain,(
% 2.82/0.74    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | ~spl7_29),
% 2.82/0.74    inference(avatar_component_clause,[],[f261])).
% 2.82/0.74  fof(f621,plain,(
% 2.82/0.74    spl7_70 | ~spl7_21 | ~spl7_48),
% 2.82/0.74    inference(avatar_split_clause,[],[f580,f365,f194,f582])).
% 2.82/0.74  fof(f580,plain,(
% 2.82/0.74    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_21 | ~spl7_48)),
% 2.82/0.74    inference(forward_demodulation,[],[f579,f58])).
% 2.82/0.74  fof(f579,plain,(
% 2.82/0.74    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_21 | ~spl7_48)),
% 2.82/0.74    inference(superposition,[],[f257,f367])).
% 2.82/0.74  fof(f367,plain,(
% 2.82/0.74    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | ~spl7_48),
% 2.82/0.74    inference(avatar_component_clause,[],[f365])).
% 2.82/0.74  fof(f257,plain,(
% 2.82/0.74    ( ! [X0] : (k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)) ) | ~spl7_21),
% 2.82/0.74    inference(superposition,[],[f255,f81])).
% 2.82/0.74  fof(f575,plain,(
% 2.82/0.74    spl7_29 | ~spl7_21 | ~spl7_28),
% 2.82/0.74    inference(avatar_split_clause,[],[f572,f240,f194,f261])).
% 2.82/0.74  fof(f572,plain,(
% 2.82/0.74    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK2),sK3) | (~spl7_21 | ~spl7_28)),
% 2.82/0.74    inference(superposition,[],[f255,f242])).
% 2.82/0.74  fof(f571,plain,(
% 2.82/0.74    ~spl7_22 | spl7_44 | ~spl7_35),
% 2.82/0.74    inference(avatar_split_clause,[],[f569,f295,f344,f199])).
% 2.82/0.74  fof(f344,plain,(
% 2.82/0.74    spl7_44 <=> ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.82/0.74  fof(f295,plain,(
% 2.82/0.74    spl7_35 <=> sK3 = k1_relat_1(sK5)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.82/0.74  fof(f569,plain,(
% 2.82/0.74    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_35),
% 2.82/0.74    inference(superposition,[],[f62,f297])).
% 2.82/0.74  fof(f297,plain,(
% 2.82/0.74    sK3 = k1_relat_1(sK5) | ~spl7_35),
% 2.82/0.74    inference(avatar_component_clause,[],[f295])).
% 2.82/0.74  fof(f568,plain,(
% 2.82/0.74    spl7_34 | ~spl7_13 | ~spl7_11),
% 2.82/0.74    inference(avatar_split_clause,[],[f559,f142,f152,f290])).
% 2.82/0.74  fof(f559,plain,(
% 2.82/0.74    ( ! [X0] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | ~spl7_11),
% 2.82/0.74    inference(resolution,[],[f144,f77])).
% 2.82/0.74  fof(f77,plain,(
% 2.82/0.74    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f40])).
% 2.82/0.74  fof(f40,plain,(
% 2.82/0.74    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.82/0.74    inference(flattening,[],[f39])).
% 2.82/0.74  fof(f39,plain,(
% 2.82/0.74    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.82/0.74    inference(ennf_transformation,[],[f15])).
% 2.82/0.74  fof(f15,axiom,(
% 2.82/0.74    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.82/0.74  fof(f558,plain,(
% 2.82/0.74    ~spl7_22 | spl7_35 | ~spl7_24 | ~spl7_31),
% 2.82/0.74    inference(avatar_split_clause,[],[f557,f273,f211,f295,f199])).
% 2.82/0.74  fof(f211,plain,(
% 2.82/0.74    spl7_24 <=> v4_relat_1(sK5,sK3)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.82/0.74  fof(f273,plain,(
% 2.82/0.74    spl7_31 <=> v1_partfun1(sK5,sK3)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 2.82/0.74  fof(f557,plain,(
% 2.82/0.74    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl7_31),
% 2.82/0.74    inference(resolution,[],[f275,f70])).
% 2.82/0.74  fof(f70,plain,(
% 2.82/0.74    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f34])).
% 2.82/0.74  fof(f34,plain,(
% 2.82/0.74    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/0.74    inference(flattening,[],[f33])).
% 2.82/0.74  fof(f33,plain,(
% 2.82/0.74    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.82/0.74    inference(ennf_transformation,[],[f14])).
% 2.82/0.74  fof(f14,axiom,(
% 2.82/0.74    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 2.82/0.74  fof(f275,plain,(
% 2.82/0.74    v1_partfun1(sK5,sK3) | ~spl7_31),
% 2.82/0.74    inference(avatar_component_clause,[],[f273])).
% 2.82/0.74  fof(f556,plain,(
% 2.82/0.74    spl7_28 | ~spl7_27),
% 2.82/0.74    inference(avatar_split_clause,[],[f555,f233,f240])).
% 2.82/0.74  fof(f233,plain,(
% 2.82/0.74    spl7_27 <=> r1_xboole_0(sK2,sK3)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 2.82/0.74  fof(f555,plain,(
% 2.82/0.74    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_27),
% 2.82/0.74    inference(resolution,[],[f235,f82])).
% 2.82/0.74  fof(f82,plain,(
% 2.82/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.82/0.74    inference(definition_unfolding,[],[f72,f65])).
% 2.82/0.74  fof(f72,plain,(
% 2.82/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f1])).
% 2.82/0.74  fof(f235,plain,(
% 2.82/0.74    r1_xboole_0(sK2,sK3) | ~spl7_27),
% 2.82/0.74    inference(avatar_component_clause,[],[f233])).
% 2.82/0.74  fof(f545,plain,(
% 2.82/0.74    spl7_4 | spl7_27 | spl7_7 | ~spl7_5),
% 2.82/0.74    inference(avatar_split_clause,[],[f544,f112,f122,f233,f107])).
% 2.82/0.74  fof(f112,plain,(
% 2.82/0.74    spl7_5 <=> r1_subset_1(sK2,sK3)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.82/0.74  fof(f544,plain,(
% 2.82/0.74    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl7_5),
% 2.82/0.74    inference(resolution,[],[f114,f68])).
% 2.82/0.74  fof(f68,plain,(
% 2.82/0.74    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f32])).
% 2.82/0.74  fof(f32,plain,(
% 2.82/0.74    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.82/0.74    inference(flattening,[],[f31])).
% 2.82/0.74  fof(f31,plain,(
% 2.82/0.74    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.82/0.74    inference(ennf_transformation,[],[f9])).
% 2.82/0.74  fof(f9,axiom,(
% 2.82/0.74    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.82/0.74  fof(f114,plain,(
% 2.82/0.74    r1_subset_1(sK2,sK3) | ~spl7_5),
% 2.82/0.74    inference(avatar_component_clause,[],[f112])).
% 2.82/0.74  fof(f489,plain,(
% 2.82/0.74    spl7_62 | ~spl7_27 | ~spl7_44),
% 2.82/0.74    inference(avatar_split_clause,[],[f475,f344,f233,f486])).
% 2.82/0.74  fof(f475,plain,(
% 2.82/0.74    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl7_27 | ~spl7_44)),
% 2.82/0.74    inference(resolution,[],[f345,f235])).
% 2.82/0.74  fof(f345,plain,(
% 2.82/0.74    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_44),
% 2.82/0.74    inference(avatar_component_clause,[],[f344])).
% 2.82/0.74  fof(f468,plain,(
% 2.82/0.74    ~spl7_21 | spl7_36 | ~spl7_32),
% 2.82/0.74    inference(avatar_split_clause,[],[f466,f279,f302,f194])).
% 2.82/0.74  fof(f466,plain,(
% 2.82/0.74    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_32),
% 2.82/0.74    inference(superposition,[],[f62,f281])).
% 2.82/0.74  fof(f465,plain,(
% 2.82/0.74    spl7_33 | ~spl7_10 | ~spl7_8),
% 2.82/0.74    inference(avatar_split_clause,[],[f456,f127,f137,f286])).
% 2.82/0.74  fof(f456,plain,(
% 2.82/0.74    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_8),
% 2.82/0.74    inference(resolution,[],[f129,f77])).
% 2.82/0.74  fof(f455,plain,(
% 2.82/0.74    ~spl7_21 | spl7_32 | ~spl7_23 | ~spl7_30),
% 2.82/0.74    inference(avatar_split_clause,[],[f454,f268,f206,f279,f194])).
% 2.82/0.74  fof(f206,plain,(
% 2.82/0.74    spl7_23 <=> v4_relat_1(sK4,sK2)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.82/0.74  fof(f268,plain,(
% 2.82/0.74    spl7_30 <=> v1_partfun1(sK4,sK2)),
% 2.82/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 2.82/0.74  fof(f454,plain,(
% 2.82/0.74    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl7_30),
% 2.82/0.74    inference(resolution,[],[f270,f70])).
% 2.82/0.74  fof(f270,plain,(
% 2.82/0.74    v1_partfun1(sK4,sK2) | ~spl7_30),
% 2.82/0.74    inference(avatar_component_clause,[],[f268])).
% 2.82/0.74  fof(f450,plain,(
% 2.82/0.74    spl7_1 | spl7_4 | spl7_37 | ~spl7_3),
% 2.82/0.74    inference(avatar_split_clause,[],[f445,f102,f310,f107,f92])).
% 2.82/0.74  fof(f445,plain,(
% 2.82/0.74    ( ! [X10,X8,X11,X9] : (v1_xboole_0(X8) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X9) | ~m1_subset_1(X9,k1_zfmisc_1(sK0)) | ~v1_funct_1(X10) | ~v1_funct_2(X10,sK2,X8) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(sK2,X8))) | ~v1_funct_1(X11) | ~v1_funct_2(X11,X9,X8) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X8))) | v1_funct_1(k1_tmap_1(sK0,X8,sK2,X9,X10,X11))) ) | ~spl7_3),
% 2.82/0.74    inference(resolution,[],[f104,f78])).
% 2.82/0.74  fof(f78,plain,(
% 2.82/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 2.82/0.74    inference(cnf_transformation,[],[f42])).
% 2.82/0.74  fof(f42,plain,(
% 2.82/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.82/0.74    inference(flattening,[],[f41])).
% 2.82/0.74  fof(f41,plain,(
% 2.82/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.82/0.74    inference(ennf_transformation,[],[f17])).
% 2.82/0.74  fof(f17,axiom,(
% 2.82/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.82/0.74  fof(f104,plain,(
% 2.82/0.74    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl7_3),
% 2.82/0.74    inference(avatar_component_clause,[],[f102])).
% 2.82/0.74  fof(f449,plain,(
% 2.82/0.74    spl7_1 | spl7_4 | spl7_41 | ~spl7_3),
% 2.82/0.74    inference(avatar_split_clause,[],[f444,f102,f330,f107,f92])).
% 2.82/0.74  fof(f444,plain,(
% 2.82/0.74    ( ! [X6,X4,X7,X5] : (v1_xboole_0(X4) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | v1_funct_2(k1_tmap_1(sK0,X4,sK2,X5,X6,X7),k4_subset_1(sK0,sK2,X5),X4)) ) | ~spl7_3),
% 2.82/0.74    inference(resolution,[],[f104,f79])).
% 2.82/0.74  fof(f79,plain,(
% 2.82/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f42])).
% 2.82/0.74  fof(f448,plain,(
% 2.82/0.74    spl7_1 | spl7_4 | spl7_45 | ~spl7_3),
% 2.82/0.74    inference(avatar_split_clause,[],[f443,f102,f352,f107,f92])).
% 2.82/0.74  fof(f443,plain,(
% 2.82/0.74    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl7_3),
% 2.82/0.74    inference(resolution,[],[f104,f80])).
% 2.82/0.74  fof(f80,plain,(
% 2.82/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 2.82/0.74    inference(cnf_transformation,[],[f42])).
% 2.82/0.74  fof(f276,plain,(
% 2.82/0.74    spl7_31 | ~spl7_12 | ~spl7_13 | spl7_2 | ~spl7_11),
% 2.82/0.74    inference(avatar_split_clause,[],[f266,f142,f97,f152,f147,f273])).
% 2.82/0.74  fof(f266,plain,(
% 2.82/0.74    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl7_11),
% 2.82/0.74    inference(resolution,[],[f66,f144])).
% 2.82/0.74  fof(f66,plain,(
% 2.82/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f30])).
% 2.82/0.74  fof(f30,plain,(
% 2.82/0.74    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.82/0.74    inference(flattening,[],[f29])).
% 2.82/0.74  fof(f29,plain,(
% 2.82/0.74    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.82/0.74    inference(ennf_transformation,[],[f13])).
% 2.82/0.74  fof(f13,axiom,(
% 2.82/0.74    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.82/0.74  fof(f271,plain,(
% 2.82/0.74    spl7_30 | ~spl7_9 | ~spl7_10 | spl7_2 | ~spl7_8),
% 2.82/0.74    inference(avatar_split_clause,[],[f265,f127,f97,f137,f132,f268])).
% 2.82/0.74  fof(f265,plain,(
% 2.82/0.74    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl7_8),
% 2.82/0.74    inference(resolution,[],[f66,f129])).
% 2.82/0.74  fof(f214,plain,(
% 2.82/0.74    spl7_24 | ~spl7_11),
% 2.82/0.74    inference(avatar_split_clause,[],[f204,f142,f211])).
% 2.82/0.74  fof(f204,plain,(
% 2.82/0.74    v4_relat_1(sK5,sK3) | ~spl7_11),
% 2.82/0.74    inference(resolution,[],[f76,f144])).
% 2.82/0.74  fof(f76,plain,(
% 2.82/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f38])).
% 2.82/0.74  fof(f38,plain,(
% 2.82/0.74    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.74    inference(ennf_transformation,[],[f21])).
% 2.82/0.74  fof(f21,plain,(
% 2.82/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.82/0.74    inference(pure_predicate_removal,[],[f11])).
% 2.82/0.74  fof(f11,axiom,(
% 2.82/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.82/0.74  fof(f209,plain,(
% 2.82/0.74    spl7_23 | ~spl7_8),
% 2.82/0.74    inference(avatar_split_clause,[],[f203,f127,f206])).
% 2.82/0.74  fof(f203,plain,(
% 2.82/0.74    v4_relat_1(sK4,sK2) | ~spl7_8),
% 2.82/0.74    inference(resolution,[],[f76,f129])).
% 2.82/0.74  fof(f202,plain,(
% 2.82/0.74    spl7_22 | ~spl7_11),
% 2.82/0.74    inference(avatar_split_clause,[],[f192,f142,f199])).
% 2.82/0.74  fof(f192,plain,(
% 2.82/0.74    v1_relat_1(sK5) | ~spl7_11),
% 2.82/0.74    inference(resolution,[],[f75,f144])).
% 2.82/0.74  fof(f75,plain,(
% 2.82/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.82/0.74    inference(cnf_transformation,[],[f37])).
% 2.82/0.74  fof(f37,plain,(
% 2.82/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.74    inference(ennf_transformation,[],[f10])).
% 2.82/0.74  fof(f10,axiom,(
% 2.82/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.82/0.74  fof(f197,plain,(
% 2.82/0.74    spl7_21 | ~spl7_8),
% 2.82/0.74    inference(avatar_split_clause,[],[f191,f127,f194])).
% 2.82/0.74  fof(f191,plain,(
% 2.82/0.74    v1_relat_1(sK4) | ~spl7_8),
% 2.82/0.74    inference(resolution,[],[f75,f129])).
% 2.82/0.74  fof(f168,plain,(
% 2.82/0.74    ~spl7_14 | ~spl7_15 | ~spl7_16),
% 2.82/0.74    inference(avatar_split_clause,[],[f43,f165,f161,f157])).
% 2.82/0.74  fof(f43,plain,(
% 2.82/0.74    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f23,plain,(
% 2.82/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.82/0.74    inference(flattening,[],[f22])).
% 2.82/0.74  fof(f22,plain,(
% 2.82/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.82/0.74    inference(ennf_transformation,[],[f19])).
% 2.82/0.74  fof(f19,negated_conjecture,(
% 2.82/0.74    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.82/0.74    inference(negated_conjecture,[],[f18])).
% 2.82/0.74  fof(f18,conjecture,(
% 2.82/0.74    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.82/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.82/0.74  fof(f155,plain,(
% 2.82/0.74    spl7_13),
% 2.82/0.74    inference(avatar_split_clause,[],[f44,f152])).
% 2.82/0.74  fof(f44,plain,(
% 2.82/0.74    v1_funct_1(sK5)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f150,plain,(
% 2.82/0.74    spl7_12),
% 2.82/0.74    inference(avatar_split_clause,[],[f45,f147])).
% 2.82/0.74  fof(f45,plain,(
% 2.82/0.74    v1_funct_2(sK5,sK3,sK1)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f145,plain,(
% 2.82/0.74    spl7_11),
% 2.82/0.74    inference(avatar_split_clause,[],[f46,f142])).
% 2.82/0.74  fof(f46,plain,(
% 2.82/0.74    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f140,plain,(
% 2.82/0.74    spl7_10),
% 2.82/0.74    inference(avatar_split_clause,[],[f47,f137])).
% 2.82/0.74  fof(f47,plain,(
% 2.82/0.74    v1_funct_1(sK4)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f135,plain,(
% 2.82/0.74    spl7_9),
% 2.82/0.74    inference(avatar_split_clause,[],[f48,f132])).
% 2.82/0.74  fof(f48,plain,(
% 2.82/0.74    v1_funct_2(sK4,sK2,sK1)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f130,plain,(
% 2.82/0.74    spl7_8),
% 2.82/0.74    inference(avatar_split_clause,[],[f49,f127])).
% 2.82/0.74  fof(f49,plain,(
% 2.82/0.74    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f125,plain,(
% 2.82/0.74    ~spl7_7),
% 2.82/0.74    inference(avatar_split_clause,[],[f50,f122])).
% 2.82/0.74  fof(f50,plain,(
% 2.82/0.74    ~v1_xboole_0(sK3)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f120,plain,(
% 2.82/0.74    spl7_6),
% 2.82/0.74    inference(avatar_split_clause,[],[f51,f117])).
% 2.82/0.74  fof(f51,plain,(
% 2.82/0.74    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f115,plain,(
% 2.82/0.74    spl7_5),
% 2.82/0.74    inference(avatar_split_clause,[],[f52,f112])).
% 2.82/0.74  fof(f52,plain,(
% 2.82/0.74    r1_subset_1(sK2,sK3)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f110,plain,(
% 2.82/0.74    ~spl7_4),
% 2.82/0.74    inference(avatar_split_clause,[],[f53,f107])).
% 2.82/0.74  fof(f53,plain,(
% 2.82/0.74    ~v1_xboole_0(sK2)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f105,plain,(
% 2.82/0.74    spl7_3),
% 2.82/0.74    inference(avatar_split_clause,[],[f54,f102])).
% 2.82/0.74  fof(f54,plain,(
% 2.82/0.74    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f100,plain,(
% 2.82/0.74    ~spl7_2),
% 2.82/0.74    inference(avatar_split_clause,[],[f55,f97])).
% 2.82/0.74  fof(f55,plain,(
% 2.82/0.74    ~v1_xboole_0(sK1)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  fof(f95,plain,(
% 2.82/0.74    ~spl7_1),
% 2.82/0.74    inference(avatar_split_clause,[],[f56,f92])).
% 2.82/0.74  fof(f56,plain,(
% 2.82/0.74    ~v1_xboole_0(sK0)),
% 2.82/0.74    inference(cnf_transformation,[],[f23])).
% 2.82/0.74  % SZS output end Proof for theBenchmark
% 2.82/0.74  % (21314)------------------------------
% 2.82/0.74  % (21314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.74  % (21314)Termination reason: Refutation
% 2.82/0.74  
% 2.82/0.74  % (21314)Memory used [KB]: 12025
% 2.82/0.74  % (21314)Time elapsed: 0.292 s
% 2.82/0.74  % (21314)------------------------------
% 2.82/0.74  % (21314)------------------------------
% 2.82/0.75  % (21294)Success in time 0.389 s
%------------------------------------------------------------------------------
