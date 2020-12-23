%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 223 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  215 ( 360 expanded)
%              Number of equality atoms :   74 ( 164 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f498,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f98,f143,f180,f279,f297,f497])).

fof(f497,plain,
    ( ~ spl2_5
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl2_5
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f495,f278])).

fof(f278,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl2_6
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f495,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f296,f492])).

fof(f492,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f477,f70])).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f477,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f191,f179])).

fof(f179,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl2_5
  <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f191,plain,(
    ! [X14,X15] : k9_relat_1(k6_partfun1(X14),X15) = k2_relat_1(k7_relat_1(k6_partfun1(X15),X14)) ),
    inference(superposition,[],[f70,f117])).

fof(f117,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0)) ),
    inference(backward_demodulation,[],[f103,f113])).

fof(f113,plain,(
    ! [X12,X13] : k1_setfam_1(k2_enumset1(X12,X12,X12,X13)) = k9_relat_1(k6_partfun1(X12),X13) ),
    inference(forward_demodulation,[],[f111,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f111,plain,(
    ! [X12,X13] : k1_setfam_1(k2_enumset1(X12,X12,X12,X13)) = k2_relat_1(k7_relat_1(k6_partfun1(X12),X13)) ),
    inference(superposition,[],[f70,f101])).

fof(f101,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(backward_demodulation,[],[f73,f99])).

fof(f99,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) = k7_relat_1(k6_partfun1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f64,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f51,f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f36,f36,f36,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f103,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(superposition,[],[f101,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f60,f60])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f296,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl2_7
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f297,plain,
    ( spl2_7
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f240,f95,f294])).

fof(f95,plain,
    ( spl2_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f240,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f97,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f136,f71])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) ) ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f54,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f41,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f97,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f279,plain,
    ( ~ spl2_6
    | spl2_2 ),
    inference(avatar_split_clause,[],[f239,f81,f276])).

fof(f81,plain,
    ( spl2_2
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f239,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_2 ),
    inference(superposition,[],[f83,f131])).

fof(f131,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f62,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f83,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f180,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f163,f140,f177])).

fof(f140,plain,
    ( spl2_4
  <=> v4_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f163,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f64,f142,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f142,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f120,f95,f140])).

fof(f120,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f64,f68,f97,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

% (12183)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f68,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f98,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f85,f76,f95])).

fof(f76,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f85,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f78,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f84,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f79,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:00:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (12182)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (12169)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (12168)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (12167)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (12182)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f498,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f79,f84,f98,f143,f180,f279,f297,f497])).
% 0.21/0.48  fof(f497,plain,(
% 0.21/0.48    ~spl2_5 | spl2_6 | ~spl2_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f496])).
% 0.21/0.48  fof(f496,plain,(
% 0.21/0.48    $false | (~spl2_5 | spl2_6 | ~spl2_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f495,f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f276])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    spl2_6 <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f495,plain,(
% 0.21/0.48    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | (~spl2_5 | ~spl2_7)),
% 0.21/0.48    inference(backward_demodulation,[],[f296,f492])).
% 0.21/0.48  fof(f492,plain,(
% 0.21/0.48    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | ~spl2_5),
% 0.21/0.48    inference(forward_demodulation,[],[f477,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f46,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,axiom,(
% 0.21/0.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f477,plain,(
% 0.21/0.48    k2_relat_1(k6_partfun1(sK1)) = k9_relat_1(k6_partfun1(sK0),sK1) | ~spl2_5),
% 0.21/0.48    inference(superposition,[],[f191,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl2_5 <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X14,X15] : (k9_relat_1(k6_partfun1(X14),X15) = k2_relat_1(k7_relat_1(k6_partfun1(X15),X14))) )),
% 0.21/0.48    inference(superposition,[],[f70,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f103,f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X12,X13] : (k1_setfam_1(k2_enumset1(X12,X12,X12,X13)) = k9_relat_1(k6_partfun1(X12),X13)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f111,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f64,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f38,f36])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X12,X13] : (k1_setfam_1(k2_enumset1(X12,X12,X12,X13)) = k2_relat_1(k7_relat_1(k6_partfun1(X12),X13))) )),
% 0.21/0.48    inference(superposition,[],[f70,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f73,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) = k7_relat_1(k6_partfun1(X1),X0)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f64,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f51,f36])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f50,f36,f36,f36,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f49,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f48,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(superposition,[],[f101,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f47,f60,f60])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1)) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f294])).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    spl2_7 <=> sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    spl2_7 | ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f240,f95,f294])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    sK1 = k10_relat_1(k6_partfun1(sK0),k9_relat_1(k6_partfun1(sK0),sK1)) | ~spl2_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f97,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1) )),
% 0.21/0.48    inference(forward_demodulation,[],[f136,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f45,f36])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f64])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f36])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k9_relat_1(k6_partfun1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_partfun1(X0))) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f54,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f41,f36])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    ~spl2_6 | spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f239,f81,f276])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl2_2 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl2_2),
% 0.21/0.48    inference(superposition,[],[f83,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f37,f36])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl2_5 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f163,f140,f177])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl2_4 <=> v4_relat_1(k6_partfun1(sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl2_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f64,f142,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl2_4 | ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f95,f140])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl2_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f64,f68,f97,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % (12183)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f43,f36])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl2_3 | ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f85,f76,f95])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl2_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f78,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f19])).
% 0.21/0.48  fof(f19,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12182)------------------------------
% 0.21/0.48  % (12182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12182)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12182)Memory used [KB]: 11001
% 0.21/0.48  % (12182)Time elapsed: 0.021 s
% 0.21/0.48  % (12182)------------------------------
% 0.21/0.48  % (12182)------------------------------
% 0.21/0.48  % (12164)Success in time 0.118 s
%------------------------------------------------------------------------------
