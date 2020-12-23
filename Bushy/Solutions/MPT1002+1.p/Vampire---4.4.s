%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t50_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:46 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 154 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  254 ( 493 expanded)
%              Number of equality atoms :   66 ( 135 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f584,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f108,f112,f135,f139,f145,f153,f198,f250,f504,f582,f583])).

fof(f583,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 != sK0
    | k1_relat_1(sK3) = sK0 ),
    introduced(theory_axiom,[])).

fof(f582,plain,
    ( spl5_24
    | ~ spl5_30
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f521,f248,f196,f164])).

fof(f164,plain,
    ( spl5_24
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f196,plain,
    ( spl5_30
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f248,plain,
    ( spl5_46
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f521,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_30
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f520,f197])).

fof(f197,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f196])).

fof(f520,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f253,f261])).

fof(f261,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_46 ),
    inference(resolution,[],[f249,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',redefinition_k1_relset_1)).

fof(f249,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f248])).

fof(f253,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_46 ),
    inference(resolution,[],[f249,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',d1_funct_2)).

fof(f504,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_17
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f502,f144])).

fof(f144,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_17
  <=> ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f502,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(resolution,[],[f184,f91])).

fof(f91,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_0
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0))) )
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f183,f134])).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK3)
        | r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0))) )
    | ~ spl5_20 ),
    inference(superposition,[],[f73,f152])).

fof(f152,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_20
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',t146_funct_1)).

fof(f250,plain,
    ( spl5_46
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f168,f110,f103,f248])).

fof(f103,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( spl5_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f168,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(superposition,[],[f111,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f198,plain,
    ( spl5_30
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f170,f103,f95,f196])).

fof(f95,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f170,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f96,f104])).

fof(f96,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f153,plain,
    ( spl5_20
    | ~ spl5_2
    | spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f131,f110,f106,f95,f151])).

fof(f106,plain,
    ( spl5_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f131,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f122,f129])).

fof(f129,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f128,f96])).

fof(f128,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f120,f107])).

fof(f107,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f122,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f80])).

fof(f145,plain,
    ( ~ spl5_17
    | ~ spl5_10
    | spl5_15 ),
    inference(avatar_split_clause,[],[f141,f137,f110,f143])).

fof(f137,plain,
    ( spl5_15
  <=> ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f141,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f140,f117])).

fof(f117,plain,
    ( ! [X2] : k7_relset_1(sK0,sK1,sK3,X2) = k9_relat_1(sK3,X2)
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',redefinition_k7_relset_1)).

fof(f140,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f138,f115])).

fof(f115,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',redefinition_k8_relset_1)).

fof(f138,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f58,f137])).

fof(f58,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',t50_funct_2)).

fof(f135,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f123,f110,f133])).

fof(f123,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f111,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t50_funct_2.p',cc1_relset_1)).

fof(f112,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f56,f110])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,
    ( spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f54,f106,f103])).

fof(f54,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f55,f95])).

fof(f55,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f57,f90])).

fof(f57,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
