%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 318 expanded)
%              Number of leaves         :   29 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  207 ( 462 expanded)
%              Number of equality atoms :   79 ( 251 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f480,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f95,f115,f121,f170,f401,f457,f479])).

fof(f479,plain,
    ( spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f478,f454,f398])).

fof(f398,plain,
    ( spl2_16
  <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f454,plain,
    ( spl2_17
  <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f478,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f475,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f475,plain,
    ( k9_relat_1(k6_partfun1(sK0),sK1) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl2_17 ),
    inference(superposition,[],[f319,f456])).

fof(f456,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f454])).

fof(f319,plain,(
    ! [X17,X16] : k1_relat_1(k7_relat_1(k6_partfun1(X16),X17)) = k9_relat_1(k6_partfun1(X16),X17) ),
    inference(superposition,[],[f74,f283])).

fof(f283,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X0),X1)) ),
    inference(backward_demodulation,[],[f175,f198])).

fof(f198,plain,(
    ! [X14,X15] : k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k9_relat_1(k6_partfun1(X14),X15) ),
    inference(forward_demodulation,[],[f188,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f67,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f188,plain,(
    ! [X14,X15] : k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k2_relat_1(k7_relat_1(k6_partfun1(X14),X15)) ),
    inference(superposition,[],[f73,f175])).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f175,plain,(
    ! [X0,X1] : k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1) ),
    inference(backward_demodulation,[],[f76,f106])).

fof(f106,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) = k7_relat_1(k6_partfun1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f67,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f53,f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f76,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f37,f37,f37,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f457,plain,
    ( spl2_17
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f416,f167,f454])).

fof(f167,plain,
    ( spl2_6
  <=> sK1 = k9_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f416,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_6 ),
    inference(superposition,[],[f413,f169])).

fof(f169,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f413,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0)) ),
    inference(forward_demodulation,[],[f179,f198])).

fof(f179,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f175,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f49,f62,f62])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f401,plain,
    ( ~ spl2_16
    | spl2_1 ),
    inference(avatar_split_clause,[],[f396,f79,f398])).

fof(f79,plain,
    ( spl2_1
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f396,plain,
    ( sK1 != k9_relat_1(k6_partfun1(sK0),sK1)
    | spl2_1 ),
    inference(superposition,[],[f81,f243])).

fof(f243,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f141,f137])).

fof(f137,plain,(
    ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f135,f64])).

fof(f64,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f38,f37,f37])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f135,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f67,f66,f68,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f43,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f66,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f141,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f65,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f81,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f170,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f165,f118,f167])).

fof(f118,plain,
    ( spl2_5
  <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f165,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f163,f73])).

fof(f163,plain,
    ( k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f102,f120])).

fof(f120,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f116,f112,f118])).

fof(f112,plain,
    ( spl2_4
  <=> v4_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f116,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f67,f114,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f114,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f108,f91,f112])).

fof(f91,plain,
    ( spl2_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f108,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f93,f71,f67,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f71,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f93,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f95,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f89,f84,f91])).

fof(f84,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f58,f86])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f87,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f82,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:14:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (17439)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (17436)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (17443)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (17431)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (17432)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (17436)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f480,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f82,f87,f95,f115,f121,f170,f401,f457,f479])).
% 0.22/0.47  fof(f479,plain,(
% 0.22/0.47    spl2_16 | ~spl2_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f478,f454,f398])).
% 0.22/0.47  fof(f398,plain,(
% 0.22/0.47    spl2_16 <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f454,plain,(
% 0.22/0.47    spl2_17 <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.47  fof(f478,plain,(
% 0.22/0.47    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | ~spl2_17),
% 0.22/0.47    inference(forward_demodulation,[],[f475,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f47,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,axiom,(
% 0.22/0.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f475,plain,(
% 0.22/0.47    k9_relat_1(k6_partfun1(sK0),sK1) = k1_relat_1(k6_partfun1(sK1)) | ~spl2_17),
% 0.22/0.47    inference(superposition,[],[f319,f456])).
% 0.22/0.47  fof(f456,plain,(
% 0.22/0.47    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1) | ~spl2_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f454])).
% 0.22/0.47  fof(f319,plain,(
% 0.22/0.47    ( ! [X17,X16] : (k1_relat_1(k7_relat_1(k6_partfun1(X16),X17)) = k9_relat_1(k6_partfun1(X16),X17)) )),
% 0.22/0.47    inference(superposition,[],[f74,f283])).
% 0.22/0.47  fof(f283,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X0),X1))) )),
% 0.22/0.47    inference(backward_demodulation,[],[f175,f198])).
% 0.22/0.47  fof(f198,plain,(
% 0.22/0.47    ( ! [X14,X15] : (k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k9_relat_1(k6_partfun1(X14),X15)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f188,f102])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f67,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f40,f37])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    ( ! [X14,X15] : (k1_setfam_1(k2_enumset1(X14,X14,X14,X15)) = k2_relat_1(k7_relat_1(k6_partfun1(X14),X15))) )),
% 0.22/0.47    inference(superposition,[],[f73,f175])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f48,f37])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f175,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f76,f106])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)) = k7_relat_1(k6_partfun1(X1),X0)) )),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f67,f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f53,f37])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f52,f37,f37,f37,f63])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f51,f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f50,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.47  fof(f457,plain,(
% 0.22/0.47    spl2_17 | ~spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f416,f167,f454])).
% 0.22/0.47  fof(f167,plain,(
% 0.22/0.47    spl2_6 <=> sK1 = k9_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f416,plain,(
% 0.22/0.47    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK0),sK1) | ~spl2_6),
% 0.22/0.47    inference(superposition,[],[f413,f169])).
% 0.22/0.47  fof(f169,plain,(
% 0.22/0.47    sK1 = k9_relat_1(k6_partfun1(sK1),sK0) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f167])).
% 0.22/0.47  fof(f413,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k9_relat_1(k6_partfun1(X1),X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f179,f198])).
% 0.22/0.47  fof(f179,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k6_partfun1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.22/0.47    inference(superposition,[],[f175,f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f49,f62,f62])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f401,plain,(
% 0.22/0.47    ~spl2_16 | spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f396,f79,f398])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    spl2_1 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f396,plain,(
% 0.22/0.47    sK1 != k9_relat_1(k6_partfun1(sK0),sK1) | spl2_1),
% 0.22/0.47    inference(superposition,[],[f81,f243])).
% 0.22/0.47  fof(f243,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f141,f137])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f135,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f38,f37,f37])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,axiom,(
% 0.22/0.47    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k9_relat_1(k2_funct_1(k6_partfun1(X0)),X1)) )),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f67,f66,f68,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f43,f37])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f41,f37])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f65,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f37])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    spl2_6 | ~spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f165,f118,f167])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl2_5 <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    sK1 = k9_relat_1(k6_partfun1(sK1),sK0) | ~spl2_5),
% 0.22/0.48    inference(forward_demodulation,[],[f163,f73])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    k9_relat_1(k6_partfun1(sK1),sK0) = k2_relat_1(k6_partfun1(sK1)) | ~spl2_5),
% 0.22/0.48    inference(superposition,[],[f102,f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    spl2_5 | ~spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f116,f112,f118])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl2_4 <=> v4_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl2_4),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f67,f114,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f112])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    spl2_4 | ~spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f108,f91,f112])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl2_3 <=> r1_tarski(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl2_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f93,f71,f67,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f45,f37])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl2_3 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f89,f84,f91])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | ~spl2_2),
% 0.22/0.48    inference(resolution,[],[f58,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f84])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.48    inference(negated_conjecture,[],[f20])).
% 0.22/0.48  fof(f20,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f79])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (17436)------------------------------
% 0.22/0.48  % (17436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17436)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (17436)Memory used [KB]: 6396
% 0.22/0.48  % (17436)Time elapsed: 0.059 s
% 0.22/0.48  % (17436)------------------------------
% 0.22/0.48  % (17436)------------------------------
% 0.22/0.48  % (17429)Success in time 0.114 s
%------------------------------------------------------------------------------
