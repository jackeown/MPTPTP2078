%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t60_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 362 expanded)
%              Number of leaves         :   43 ( 149 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 ( 865 expanded)
%              Number of equality atoms :   58 ( 138 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f80,f88,f98,f108,f117,f152,f159,f173,f184,f195,f202,f211,f234,f248,f268,f281,f291,f298,f312,f350,f352,f371,f373])).

fof(f373,plain,
    ( ~ spl4_0
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f370,f362])).

fof(f362,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(sK2,X0)
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f358,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f358,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f356,f100])).

fof(f100,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X1 )
    | ~ spl4_8 ),
    inference(resolution,[],[f97,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',t8_boole)).

fof(f97,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_8
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f356,plain,
    ( ! [X0] : v1_xboole_0(k10_relat_1(sK2,X0))
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f354,f79])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f354,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK2,X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) )
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(superposition,[],[f249,f328])).

fof(f328,plain,
    ( ! [X7] : k8_relset_1(k1_xboole_0,sK0,sK2,X7) = k10_relat_1(sK2,X7)
    | ~ spl4_4 ),
    inference(resolution,[],[f58,f79])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',redefinition_k8_relset_1)).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k8_relset_1(k1_xboole_0,X1,X0,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl4_0 ),
    inference(resolution,[],[f57,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f48,f65])).

fof(f65,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',cc1_subset_1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',dt_k8_relset_1)).

fof(f370,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl4_53
  <=> k1_xboole_0 != k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f371,plain,
    ( ~ spl4_53
    | ~ spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f353,f86,f78,f369])).

fof(f86,plain,
    ( spl4_7
  <=> k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f353,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f87,f328])).

fof(f87,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f352,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_30
    | spl4_51 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_30
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f349,f341])).

fof(f341,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f337,f107])).

fof(f337,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(resolution,[],[f335,f100])).

fof(f335,plain,
    ( ! [X0] : v1_xboole_0(k10_relat_1(k1_xboole_0,X0))
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f333,f201])).

fof(f201,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_30
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f333,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(k1_xboole_0,X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) )
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(superposition,[],[f249,f326])).

fof(f326,plain,
    ( ! [X0] : k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,X0)
    | ~ spl4_30 ),
    inference(resolution,[],[f58,f201])).

fof(f349,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl4_51
  <=> k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f350,plain,
    ( ~ spl4_51
    | ~ spl4_30
    | spl4_33 ),
    inference(avatar_split_clause,[],[f332,f209,f200,f348])).

fof(f209,plain,
    ( spl4_33
  <=> k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f332,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(superposition,[],[f210,f326])).

fof(f210,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f209])).

fof(f312,plain,
    ( spl4_48
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f302,f266,f310])).

fof(f310,plain,
    ( spl4_48
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f266,plain,
    ( spl4_40
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f302,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_40 ),
    inference(superposition,[],[f49,f267])).

fof(f267,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f266])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',existence_m1_subset_1)).

fof(f298,plain,
    ( ~ spl4_47
    | spl4_39
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f282,f266,f243,f296])).

fof(f296,plain,
    ( spl4_47
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f243,plain,
    ( spl4_39
  <=> k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f282,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl4_39
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f244,f267])).

fof(f244,plain,
    ( k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f243])).

fof(f291,plain,
    ( ~ spl4_45
    | spl4_35
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f284,f266,f223,f289])).

fof(f289,plain,
    ( spl4_45
  <=> ~ v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f223,plain,
    ( spl4_35
  <=> ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f284,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl4_35
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f224,f267])).

fof(f224,plain,
    ( ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f223])).

fof(f281,plain,
    ( spl4_42
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f272,f246,f279])).

fof(f279,plain,
    ( spl4_42
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f246,plain,
    ( spl4_38
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f272,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_38 ),
    inference(superposition,[],[f49,f247])).

fof(f247,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f246])).

fof(f268,plain,
    ( spl4_40
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f259,f232,f106,f96,f266])).

fof(f232,plain,
    ( spl4_36
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f259,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f255,f107])).

fof(f255,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(resolution,[],[f233,f100])).

fof(f233,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f232])).

fof(f248,plain,
    ( spl4_38
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f239,f226,f106,f96,f246])).

fof(f226,plain,
    ( spl4_34
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f239,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f235,f107])).

fof(f235,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(resolution,[],[f227,f100])).

fof(f227,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f226])).

fof(f234,plain,
    ( spl4_34
    | spl4_36
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f214,f64,f232,f226])).

fof(f214,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_0 ),
    inference(resolution,[],[f212,f90])).

fof(f212,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f153,f49])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK3(k1_zfmisc_1(X1)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f126,f49])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',t2_subset)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',t4_subset)).

fof(f211,plain,
    ( ~ spl4_33
    | spl4_7
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f187,f171,f86,f209])).

fof(f171,plain,
    ( spl4_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f187,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(superposition,[],[f87,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f202,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f188,f171,f78,f200])).

fof(f188,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(superposition,[],[f79,f172])).

fof(f195,plain,
    ( ~ spl4_29
    | spl4_15
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f186,f171,f138,f193])).

fof(f193,plain,
    ( spl4_29
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f138,plain,
    ( spl4_15
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f186,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(superposition,[],[f139,f172])).

fof(f139,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)),sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f184,plain,
    ( spl4_24
    | spl4_26
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f174,f157,f182,f179])).

fof(f179,plain,
    ( spl4_24
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f182,plain,
    ( spl4_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f157,plain,
    ( spl4_20
  <=> ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(k1_xboole_0,sK0))
        | ~ m1_subset_1(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,sK0),X0) )
    | ~ spl4_20 ),
    inference(resolution,[],[f158,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f120,f52])).

fof(f120,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',antisymmetry_r2_hidden)).

fof(f158,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(k1_xboole_0,sK0))
        | ~ m1_subset_1(X2,sK2) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f173,plain,
    ( spl4_22
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f164,f150,f106,f96,f171])).

fof(f150,plain,
    ( spl4_18
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f164,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f160,f107])).

fof(f160,plain,
    ( sK2 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f151,f100])).

fof(f151,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f159,plain,
    ( spl4_18
    | spl4_20
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f154,f78,f157,f150])).

fof(f154,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(k1_xboole_0,sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X2,sK2) )
    | ~ spl4_4 ),
    inference(resolution,[],[f126,f79])).

fof(f152,plain,
    ( ~ spl4_15
    | spl4_16
    | spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f131,f78,f150,f144,f138])).

fof(f144,plain,
    ( spl4_16
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f131,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)),sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f122,f79])).

fof(f117,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f110,f106,f115])).

fof(f115,plain,
    ( spl4_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f110,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(superposition,[],[f49,f107])).

fof(f108,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f101,f96,f106])).

fof(f101,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(resolution,[],[f97,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',t6_boole)).

fof(f98,plain,
    ( spl4_8
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f91,f64,f96])).

fof(f91,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f90,f49])).

fof(f88,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',t60_funct_2)).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f71,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f46,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',d2_xboole_0)).

fof(f66,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f59,f64])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f46])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t60_funct_2.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
