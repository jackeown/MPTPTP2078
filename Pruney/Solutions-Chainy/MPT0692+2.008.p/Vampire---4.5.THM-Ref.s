%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:57 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  297 (1957 expanded)
%              Number of leaves         :   71 ( 733 expanded)
%              Depth                    :   14
%              Number of atoms          :  765 (3355 expanded)
%              Number of equality atoms :  166 (1604 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f103,f113,f123,f137,f153,f161,f183,f192,f205,f213,f226,f252,f263,f272,f280,f302,f322,f351,f366,f391,f588,f613,f631,f639,f661,f666,f681,f722,f805,f821,f856,f1100,f1109,f1233,f1426,f1489,f1515,f1520,f1535,f1594,f1623,f1628,f2048,f2117,f2119])).

fof(f2119,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f2118])).

fof(f2118,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f2101,f90])).

fof(f90,plain,
    ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_4
  <=> sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2101,plain,
    ( sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f497,f1822])).

fof(f1822,plain,
    ( ! [X0] : sK0 = k6_subset_1(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f1801,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f54,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1801,plain,
    ( ! [X0] : r1_xboole_0(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f85,f1670,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1670,plain,
    ( ! [X0] : r1_xboole_0(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f75,f936,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f936,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f922,f356])).

fof(f356,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f335,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f335,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f75,f143,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f143,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f141,f136])).

fof(f136,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_9
  <=> k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f141,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f922,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f75,f80,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f80,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f75,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f85,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f497,plain,
    ( ! [X12] : k9_relat_1(sK1,k10_relat_1(sK1,X12)) = k6_subset_1(X12,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12))))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f470,f65])).

fof(f65,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f470,plain,
    ( ! [X12] : k6_subset_1(X12,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))) = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X12)),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f403,f239])).

fof(f239,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f235,f70])).

fof(f235,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f75,f80,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f403,plain,(
    ! [X6,X7] : k6_subset_1(X6,k6_subset_1(X6,X7)) = k6_subset_1(X7,k6_subset_1(X7,X6)) ),
    inference(superposition,[],[f394,f67])).

fof(f67,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f48,f64,f45,f45])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f394,plain,(
    ! [X4,X5] : k6_subset_1(X4,k6_subset_1(X4,X5)) = k1_setfam_1(k3_enumset1(X5,X5,X5,X5,X4)) ),
    inference(superposition,[],[f66,f67])).

fof(f66,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f44,f64,f64])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2117,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f2116])).

fof(f2116,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f2100,f90])).

fof(f2100,plain,
    ( sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f1822,f497])).

fof(f2048,plain,
    ( spl2_52
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f1537,f1532,f2045])).

fof(f2045,plain,
    ( spl2_52
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f1532,plain,
    ( spl2_48
  <=> r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1537,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_48 ),
    inference(unit_resulting_resolution,[],[f1534,f70])).

fof(f1534,plain,
    ( r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f1532])).

fof(f1628,plain,
    ( spl2_51
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1597,f1591,f1625])).

fof(f1625,plain,
    ( spl2_51
  <=> r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f1591,plain,
    ( spl2_49
  <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f1597,plain,
    ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_49 ),
    inference(unit_resulting_resolution,[],[f1593,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1593,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1591])).

fof(f1623,plain,
    ( spl2_50
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1595,f1591,f1620])).

fof(f1620,plain,
    ( spl2_50
  <=> r1_tarski(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f1595,plain,
    ( r1_tarski(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_49 ),
    inference(unit_resulting_resolution,[],[f1593,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1594,plain,
    ( spl2_49
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1504,f1486,f189,f78,f73,f1591])).

fof(f189,plain,
    ( spl2_14
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f1486,plain,
    ( spl2_45
  <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f1504,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f1494,f191])).

fof(f191,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1494,plain,
    ( k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_45 ),
    inference(superposition,[],[f931,f1488])).

fof(f1488,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f931,plain,
    ( ! [X1] : k10_relat_1(sK1,k6_subset_1(k1_xboole_0,X1)) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(superposition,[],[f922,f191])).

fof(f1535,plain,
    ( spl2_48
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1506,f1486,f1532])).

fof(f1506,plain,
    ( r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f1496,f65])).

fof(f1496,plain,
    ( k1_xboole_0 != k6_subset_1(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_45 ),
    inference(superposition,[],[f423,f1488])).

fof(f423,plain,(
    ! [X1] :
      ( k1_xboole_0 != k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X1))
      | r1_tarski(X1,X1) ) ),
    inference(forward_demodulation,[],[f421,f67])).

fof(f421,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))
      | r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f71,f398])).

fof(f398,plain,(
    ! [X0] : k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k6_subset_1(X0,X0) ),
    inference(superposition,[],[f394,f65])).

fof(f1520,plain,
    ( spl2_47
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1492,f1486,f1517])).

fof(f1517,plain,
    ( spl2_47
  <=> r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1492,plain,
    ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_45 ),
    inference(unit_resulting_resolution,[],[f1488,f68])).

fof(f1515,plain,
    ( spl2_46
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1490,f1486,f1512])).

fof(f1512,plain,
    ( spl2_46
  <=> r1_tarski(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f1490,plain,
    ( r1_tarski(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_45 ),
    inference(unit_resulting_resolution,[],[f1488,f71])).

fof(f1489,plain,
    ( spl2_45
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f1456,f210,f189,f78,f73,f1486])).

fof(f210,plain,
    ( spl2_16
  <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f1456,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f1428,f191])).

fof(f1428,plain,
    ( k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(superposition,[],[f931,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_relat_1(sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f210])).

fof(f1426,plain,
    ( spl2_44
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1377,f802,f610,f134,f78,f73,f1423])).

fof(f1423,plain,
    ( spl2_44
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f610,plain,
    ( spl2_30
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f802,plain,
    ( spl2_37
  <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1377,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_37 ),
    inference(backward_demodulation,[],[f804,f1370])).

fof(f1370,plain,
    ( ! [X0] : k2_relat_1(sK1) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f1285,f69])).

fof(f1285,plain,
    ( ! [X0] : r1_xboole_0(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f75,f955,f51])).

fof(f955,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f935,f146])).

fof(f146,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f143,f70])).

fof(f935,plain,
    ( ! [X2] : k6_subset_1(k10_relat_1(sK1,X2),k1_relat_1(sK1)) = k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(superposition,[],[f922,f612])).

fof(f612,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f610])).

fof(f804,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f802])).

fof(f1233,plain,
    ( spl2_42
    | ~ spl2_43
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f1069,f299,f134,f78,f73,f1230,f1226])).

fof(f1226,plain,
    ( spl2_42
  <=> r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1230,plain,
    ( spl2_43
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f299,plain,
    ( spl2_22
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f1069,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(superposition,[],[f424,f1002])).

fof(f1002,plain,
    ( ! [X5] : k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(X5,k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f976,f301])).

fof(f301,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f299])).

fof(f976,plain,
    ( ! [X5] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k6_subset_1(X5,k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f239,f953])).

fof(f953,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f933,f146])).

fof(f933,plain,
    ( ! [X0] : k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f922,f136])).

fof(f424,plain,(
    ! [X2] :
      ( k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X2)) != X2
      | r1_xboole_0(X2,X2) ) ),
    inference(forward_demodulation,[],[f422,f67])).

fof(f422,plain,(
    ! [X2] :
      ( k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) != X2
      | r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f68,f398])).

fof(f1109,plain,
    ( spl2_41
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f1068,f299,f134,f78,f73,f1106])).

fof(f1106,plain,
    ( spl2_41
  <=> k1_xboole_0 = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f1068,plain,
    ( k1_xboole_0 = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(superposition,[],[f1002,f416])).

fof(f416,plain,(
    ! [X4] : k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X4)) = k6_subset_1(X4,X4) ),
    inference(superposition,[],[f398,f67])).

fof(f1100,plain,
    ( spl2_40
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f1088,f299,f134,f78,f73,f1097])).

fof(f1097,plain,
    ( spl2_40
  <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1088,plain,
    ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f1061,f65])).

fof(f1061,plain,
    ( r1_tarski(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f1002,f411])).

fof(f411,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,k6_subset_1(X1,X0))
      | r1_tarski(X0,k6_subset_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f404,f67])).

fof(f404,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))
      | r1_tarski(X0,k6_subset_1(X0,X1)) ) ),
    inference(superposition,[],[f71,f394])).

fof(f856,plain,
    ( spl2_39
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f827,f818,f853])).

fof(f853,plain,
    ( spl2_39
  <=> k1_xboole_0 = k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f818,plain,
    ( spl2_38
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f827,plain,
    ( k1_xboole_0 = k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))))
    | ~ spl2_38 ),
    inference(superposition,[],[f820,f398])).

fof(f820,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f818])).

fof(f821,plain,
    ( spl2_38
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f724,f719,f818])).

fof(f719,plain,
    ( spl2_36
  <=> r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f724,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f721,f70])).

fof(f721,plain,
    ( r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f719])).

fof(f805,plain,
    ( spl2_37
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f498,f319,f802])).

fof(f319,plain,
    ( spl2_23
  <=> k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f498,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f471,f65])).

fof(f471,plain,
    ( k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))) = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0)
    | ~ spl2_23 ),
    inference(superposition,[],[f403,f321])).

fof(f321,plain,
    ( k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f319])).

fof(f722,plain,
    ( spl2_36
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f704,f678,f719])).

fof(f678,plain,
    ( spl2_35
  <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f704,plain,
    ( r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f690,f65])).

fof(f690,plain,
    ( k1_xboole_0 != k6_subset_1(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_35 ),
    inference(superposition,[],[f423,f680])).

fof(f680,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f678])).

fof(f681,plain,
    ( spl2_35
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f644,f636,f678])).

fof(f636,plain,
    ( spl2_32
  <=> k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f644,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_32 ),
    inference(superposition,[],[f638,f416])).

fof(f638,plain,
    ( k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f636])).

fof(f666,plain,
    ( spl2_34
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f642,f636,f663])).

fof(f663,plain,
    ( spl2_34
  <=> r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f642,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f638,f429])).

fof(f429,plain,(
    ! [X2] :
      ( k1_xboole_0 != k6_subset_1(X2,X2)
      | r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,X2)) ) ),
    inference(superposition,[],[f71,f416])).

fof(f661,plain,
    ( spl2_33
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f641,f636,f658])).

fof(f658,plain,
    ( spl2_33
  <=> r1_xboole_0(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f641,plain,
    ( r1_xboole_0(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f638,f430])).

fof(f430,plain,(
    ! [X3] :
      ( k1_xboole_0 != k6_subset_1(X3,X3)
      | r1_xboole_0(k1_xboole_0,k6_subset_1(k1_xboole_0,X3)) ) ),
    inference(superposition,[],[f68,f416])).

fof(f639,plain,
    ( spl2_32
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f619,f610,f78,f73,f636])).

fof(f619,plain,
    ( k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(superposition,[],[f239,f612])).

fof(f631,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f618,f610,f78,f73,f628])).

fof(f628,plain,
    ( spl2_31
  <=> r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f618,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(superposition,[],[f235,f612])).

fof(f613,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f604,f363,f134,f73,f610])).

fof(f363,plain,
    ( spl2_25
  <=> k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f604,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f592,f65])).

fof(f592,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k6_subset_1(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_25 ),
    inference(superposition,[],[f496,f365])).

fof(f365,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f363])).

fof(f496,plain,
    ( ! [X10] : k10_relat_1(sK1,X10) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X10)))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f469,f65])).

fof(f469,plain,
    ( ! [X10] : k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X10))) = k6_subset_1(k10_relat_1(sK1,X10),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(superposition,[],[f403,f146])).

fof(f588,plain,
    ( spl2_28
    | ~ spl2_29
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f577,f100,f585,f581])).

fof(f581,plain,
    ( spl2_28
  <=> r1_xboole_0(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f585,plain,
    ( spl2_29
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f100,plain,
    ( spl2_5
  <=> k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f577,plain,
    ( sK0 != k2_relat_1(sK1)
    | r1_xboole_0(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0))
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f563,f65])).

fof(f563,plain,
    ( k2_relat_1(sK1) != k6_subset_1(sK0,k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0))
    | ~ spl2_5 ),
    inference(superposition,[],[f412,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f412,plain,(
    ! [X2,X3] :
      ( k6_subset_1(X3,k6_subset_1(X3,X2)) != X2
      | r1_xboole_0(X2,k6_subset_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f405,f67])).

fof(f405,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X2)) != X2
      | r1_xboole_0(X2,k6_subset_1(X2,X3)) ) ),
    inference(superposition,[],[f68,f394])).

fof(f391,plain,
    ( spl2_26
    | ~ spl2_27
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f326,f319,f388,f384])).

fof(f384,plain,
    ( spl2_26
  <=> r1_xboole_0(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f388,plain,
    ( spl2_27
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f326,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,k1_relat_1(sK1))
    | r1_xboole_0(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl2_23 ),
    inference(superposition,[],[f68,f321])).

fof(f366,plain,
    ( spl2_25
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f353,f348,f363])).

fof(f348,plain,
    ( spl2_24
  <=> r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f353,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f350,f70])).

fof(f350,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f348])).

fof(f351,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f336,f150,f73,f348])).

fof(f150,plain,
    ( spl2_10
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f336,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f75,f152,f50])).

fof(f152,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f322,plain,
    ( spl2_23
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f274,f269,f319])).

fof(f269,plain,
    ( spl2_20
  <=> r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f274,plain,
    ( k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f271,f70])).

fof(f271,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f269])).

fof(f302,plain,
    ( spl2_22
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f283,f277,f299])).

fof(f277,plain,
    ( spl2_21
  <=> k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f283,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl2_21 ),
    inference(superposition,[],[f279,f65])).

fof(f279,plain,
    ( k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f277])).

fof(f280,plain,
    ( spl2_21
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f256,f249,f277])).

fof(f249,plain,
    ( spl2_18
  <=> r1_tarski(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f256,plain,
    ( k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f251,f70])).

fof(f251,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f272,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f243,f134,f78,f73,f269])).

fof(f243,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f235,f136])).

fof(f263,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f245,f223,f189,f78,f73,f260])).

fof(f260,plain,
    ( spl2_19
  <=> r1_xboole_0(k9_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f223,plain,
    ( spl2_17
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f245,plain,
    ( r1_xboole_0(k9_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f240,f191])).

fof(f240,plain,
    ( r1_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f235,f229])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | r1_xboole_0(X0,k1_relat_1(sK1)) )
    | ~ spl2_17 ),
    inference(resolution,[],[f225,f60])).

fof(f225,plain,
    ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f223])).

fof(f252,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f244,f189,f78,f73,f249])).

fof(f244,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(superposition,[],[f235,f191])).

fof(f226,plain,
    ( spl2_17
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f216,f210,f223])).

fof(f216,plain,
    ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f212,f68])).

fof(f213,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f197,f189,f134,f73,f210])).

fof(f197,plain,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f146,f191])).

fof(f205,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f198,f189,f134,f73,f202])).

fof(f202,plain,
    ( spl2_15
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f198,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f143,f191])).

fof(f192,plain,
    ( spl2_14
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f186,f73,f189])).

fof(f186,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f75,f92,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f65,f68])).

fof(f183,plain,
    ( spl2_12
    | ~ spl2_13
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f165,f158,f180,f176])).

fof(f176,plain,
    ( spl2_12
  <=> r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f180,plain,
    ( spl2_13
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f158,plain,
    ( spl2_11
  <=> k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f165,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_11 ),
    inference(superposition,[],[f68,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl2_11
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f155,f150,f158])).

fof(f155,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f152,f70])).

fof(f153,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f148,f134,f73,f150])).

fof(f148,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(superposition,[],[f143,f136])).

fof(f137,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f131,f73,f134])).

fof(f131,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f123,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f115,f120])).

fof(f120,plain,
    ( spl2_8
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f115,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f65,f71])).

fof(f113,plain,
    ( spl2_6
    | ~ spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f104,f100,f110,f106])).

fof(f106,plain,
    ( spl2_6
  <=> r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f110,plain,
    ( spl2_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f104,plain,
    ( k1_xboole_0 != sK0
    | r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f68,f102])).

fof(f103,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f97,f83,f100])).

fof(f97,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f85,f70])).

fof(f91,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f41,f88])).

fof(f41,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f86,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:30:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (26209)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.42  % (26211)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.43  % (26201)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (26206)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (26198)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (26197)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (26200)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (26203)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (26207)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (26195)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (26196)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (26199)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (26210)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (26202)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (26204)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (26212)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (26208)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (26205)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 2.21/0.64  % (26203)Refutation found. Thanks to Tanya!
% 2.21/0.64  % SZS status Theorem for theBenchmark
% 2.21/0.64  % SZS output start Proof for theBenchmark
% 2.21/0.64  fof(f2120,plain,(
% 2.21/0.64    $false),
% 2.21/0.64    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f103,f113,f123,f137,f153,f161,f183,f192,f205,f213,f226,f252,f263,f272,f280,f302,f322,f351,f366,f391,f588,f613,f631,f639,f661,f666,f681,f722,f805,f821,f856,f1100,f1109,f1233,f1426,f1489,f1515,f1520,f1535,f1594,f1623,f1628,f2048,f2117,f2119])).
% 2.21/0.64  fof(f2119,plain,(
% 2.21/0.64    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_9),
% 2.21/0.64    inference(avatar_contradiction_clause,[],[f2118])).
% 2.21/0.64  fof(f2118,plain,(
% 2.21/0.64    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_9)),
% 2.21/0.64    inference(subsumption_resolution,[],[f2101,f90])).
% 2.21/0.64  fof(f90,plain,(
% 2.21/0.64    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) | spl2_4),
% 2.21/0.64    inference(avatar_component_clause,[],[f88])).
% 2.21/0.64  fof(f88,plain,(
% 2.21/0.64    spl2_4 <=> sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.21/0.64  fof(f2101,plain,(
% 2.21/0.64    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f497,f1822])).
% 2.21/0.64  fof(f1822,plain,(
% 2.21/0.64    ( ! [X0] : (sK0 = k6_subset_1(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_9)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1801,f69])).
% 2.21/0.64  fof(f69,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 2.21/0.64    inference(definition_unfolding,[],[f54,f45])).
% 2.21/0.64  fof(f45,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f10])).
% 2.21/0.64  fof(f10,axiom,(
% 2.21/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.21/0.64  fof(f54,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f36])).
% 2.21/0.64  fof(f36,plain,(
% 2.21/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.21/0.64    inference(nnf_transformation,[],[f6])).
% 2.21/0.64  fof(f6,axiom,(
% 2.21/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.21/0.64  fof(f1801,plain,(
% 2.21/0.64    ( ! [X0] : (r1_xboole_0(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_9)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f85,f1670,f60])).
% 2.21/0.64  fof(f60,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f32])).
% 2.21/0.64  fof(f32,plain,(
% 2.21/0.64    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.21/0.64    inference(flattening,[],[f31])).
% 2.21/0.64  fof(f31,plain,(
% 2.21/0.64    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.21/0.64    inference(ennf_transformation,[],[f5])).
% 2.21/0.64  fof(f5,axiom,(
% 2.21/0.64    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.21/0.64  fof(f1670,plain,(
% 2.21/0.64    ( ! [X0] : (r1_xboole_0(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f936,f51])).
% 2.21/0.64  fof(f51,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f35])).
% 2.21/0.64  fof(f35,plain,(
% 2.21/0.64    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(nnf_transformation,[],[f26])).
% 2.21/0.64  fof(f26,plain,(
% 2.21/0.64    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(ennf_transformation,[],[f14])).
% 2.21/0.64  fof(f14,axiom,(
% 2.21/0.64    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 2.21/0.64  fof(f936,plain,(
% 2.21/0.64    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f922,f356])).
% 2.21/0.64  fof(f356,plain,(
% 2.21/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f335,f70])).
% 2.21/0.64  fof(f70,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.21/0.64    inference(definition_unfolding,[],[f57,f45])).
% 2.21/0.64  fof(f57,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f37])).
% 2.21/0.64  fof(f37,plain,(
% 2.21/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.21/0.64    inference(nnf_transformation,[],[f2])).
% 2.21/0.64  fof(f2,axiom,(
% 2.21/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.21/0.64  fof(f335,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f143,f50])).
% 2.21/0.64  fof(f50,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f25])).
% 2.21/0.64  fof(f25,plain,(
% 2.21/0.64    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(flattening,[],[f24])).
% 2.21/0.64  fof(f24,plain,(
% 2.21/0.64    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(ennf_transformation,[],[f17])).
% 2.21/0.64  fof(f17,axiom,(
% 2.21/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.21/0.64  fof(f143,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(forward_demodulation,[],[f141,f136])).
% 2.21/0.64  fof(f136,plain,(
% 2.21/0.64    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) | ~spl2_9),
% 2.21/0.64    inference(avatar_component_clause,[],[f134])).
% 2.21/0.64  fof(f134,plain,(
% 2.21/0.64    spl2_9 <=> k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.21/0.64  fof(f141,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1)))) ) | ~spl2_1),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f49])).
% 2.21/0.64  fof(f49,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f23])).
% 2.21/0.64  fof(f23,plain,(
% 2.21/0.64    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(ennf_transformation,[],[f13])).
% 2.21/0.64  fof(f13,axiom,(
% 2.21/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 2.21/0.64  fof(f922,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f80,f59])).
% 2.21/0.64  fof(f59,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f30])).
% 2.21/0.64  fof(f30,plain,(
% 2.21/0.64    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.21/0.64    inference(flattening,[],[f29])).
% 2.21/0.64  fof(f29,plain,(
% 2.21/0.64    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.21/0.64    inference(ennf_transformation,[],[f15])).
% 2.21/0.64  fof(f15,axiom,(
% 2.21/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 2.21/0.64  fof(f80,plain,(
% 2.21/0.64    v1_funct_1(sK1) | ~spl2_2),
% 2.21/0.64    inference(avatar_component_clause,[],[f78])).
% 2.21/0.64  fof(f78,plain,(
% 2.21/0.64    spl2_2 <=> v1_funct_1(sK1)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.21/0.64  fof(f75,plain,(
% 2.21/0.64    v1_relat_1(sK1) | ~spl2_1),
% 2.21/0.64    inference(avatar_component_clause,[],[f73])).
% 2.21/0.64  fof(f73,plain,(
% 2.21/0.64    spl2_1 <=> v1_relat_1(sK1)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.21/0.64  fof(f85,plain,(
% 2.21/0.64    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 2.21/0.64    inference(avatar_component_clause,[],[f83])).
% 2.21/0.64  fof(f83,plain,(
% 2.21/0.64    spl2_3 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.21/0.64  fof(f497,plain,(
% 2.21/0.64    ( ! [X12] : (k9_relat_1(sK1,k10_relat_1(sK1,X12)) = k6_subset_1(X12,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12))))) ) | (~spl2_1 | ~spl2_2)),
% 2.21/0.64    inference(forward_demodulation,[],[f470,f65])).
% 2.21/0.64  fof(f65,plain,(
% 2.21/0.64    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.21/0.64    inference(definition_unfolding,[],[f42,f45])).
% 2.21/0.64  fof(f42,plain,(
% 2.21/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.64    inference(cnf_transformation,[],[f3])).
% 2.21/0.64  fof(f3,axiom,(
% 2.21/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.21/0.64  fof(f470,plain,(
% 2.21/0.64    ( ! [X12] : (k6_subset_1(X12,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))) = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X12)),k1_xboole_0)) ) | (~spl2_1 | ~spl2_2)),
% 2.21/0.64    inference(superposition,[],[f403,f239])).
% 2.21/0.64  fof(f239,plain,(
% 2.21/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f235,f70])).
% 2.21/0.64  fof(f235,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f80,f53])).
% 2.21/0.64  fof(f53,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f28])).
% 2.21/0.64  fof(f28,plain,(
% 2.21/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(flattening,[],[f27])).
% 2.21/0.64  fof(f27,plain,(
% 2.21/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.21/0.64    inference(ennf_transformation,[],[f16])).
% 2.21/0.64  fof(f16,axiom,(
% 2.21/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 2.21/0.64  fof(f403,plain,(
% 2.21/0.64    ( ! [X6,X7] : (k6_subset_1(X6,k6_subset_1(X6,X7)) = k6_subset_1(X7,k6_subset_1(X7,X6))) )),
% 2.21/0.64    inference(superposition,[],[f394,f67])).
% 2.21/0.64  fof(f67,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f48,f64,f45,f45])).
% 2.21/0.64  fof(f64,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f46,f63])).
% 2.21/0.64  fof(f63,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.21/0.64    inference(definition_unfolding,[],[f47,f62])).
% 2.21/0.64  fof(f62,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.21/0.64    inference(definition_unfolding,[],[f58,f61])).
% 2.21/0.64  fof(f61,plain,(
% 2.21/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f9])).
% 2.21/0.64  fof(f9,axiom,(
% 2.21/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.21/0.64  fof(f58,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f8])).
% 2.21/0.64  fof(f8,axiom,(
% 2.21/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.21/0.64  fof(f47,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f7])).
% 2.21/0.64  fof(f7,axiom,(
% 2.21/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.21/0.64  fof(f46,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f11])).
% 2.21/0.64  fof(f11,axiom,(
% 2.21/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.21/0.64  fof(f48,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f4])).
% 2.21/0.64  fof(f4,axiom,(
% 2.21/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.64  fof(f394,plain,(
% 2.21/0.64    ( ! [X4,X5] : (k6_subset_1(X4,k6_subset_1(X4,X5)) = k1_setfam_1(k3_enumset1(X5,X5,X5,X5,X4))) )),
% 2.21/0.64    inference(superposition,[],[f66,f67])).
% 2.21/0.64  fof(f66,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f44,f64,f64])).
% 2.21/0.64  fof(f44,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f1])).
% 2.21/0.64  fof(f1,axiom,(
% 2.21/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.21/0.64  fof(f2117,plain,(
% 2.21/0.64    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_9),
% 2.21/0.64    inference(avatar_contradiction_clause,[],[f2116])).
% 2.21/0.64  fof(f2116,plain,(
% 2.21/0.64    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_9)),
% 2.21/0.64    inference(subsumption_resolution,[],[f2100,f90])).
% 2.21/0.64  fof(f2100,plain,(
% 2.21/0.64    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f1822,f497])).
% 2.21/0.64  fof(f2048,plain,(
% 2.21/0.64    spl2_52 | ~spl2_48),
% 2.21/0.64    inference(avatar_split_clause,[],[f1537,f1532,f2045])).
% 2.21/0.64  fof(f2045,plain,(
% 2.21/0.64    spl2_52 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 2.21/0.64  fof(f1532,plain,(
% 2.21/0.64    spl2_48 <=> r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 2.21/0.64  fof(f1537,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_48),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1534,f70])).
% 2.21/0.64  fof(f1534,plain,(
% 2.21/0.64    r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_48),
% 2.21/0.64    inference(avatar_component_clause,[],[f1532])).
% 2.21/0.64  fof(f1628,plain,(
% 2.21/0.64    spl2_51 | ~spl2_49),
% 2.21/0.64    inference(avatar_split_clause,[],[f1597,f1591,f1625])).
% 2.21/0.64  fof(f1625,plain,(
% 2.21/0.64    spl2_51 <=> r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 2.21/0.64  fof(f1591,plain,(
% 2.21/0.64    spl2_49 <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 2.21/0.64  fof(f1597,plain,(
% 2.21/0.64    r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_49),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1593,f68])).
% 2.21/0.64  fof(f68,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.21/0.64    inference(definition_unfolding,[],[f55,f45])).
% 2.21/0.64  fof(f55,plain,(
% 2.21/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.21/0.64    inference(cnf_transformation,[],[f36])).
% 2.21/0.64  fof(f1593,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_49),
% 2.21/0.64    inference(avatar_component_clause,[],[f1591])).
% 2.21/0.64  fof(f1623,plain,(
% 2.21/0.64    spl2_50 | ~spl2_49),
% 2.21/0.64    inference(avatar_split_clause,[],[f1595,f1591,f1620])).
% 2.21/0.64  fof(f1620,plain,(
% 2.21/0.64    spl2_50 <=> r1_tarski(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 2.21/0.64  fof(f1595,plain,(
% 2.21/0.64    r1_tarski(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_49),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1593,f71])).
% 2.21/0.64  fof(f71,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.21/0.64    inference(definition_unfolding,[],[f56,f45])).
% 2.21/0.64  fof(f56,plain,(
% 2.21/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.21/0.64    inference(cnf_transformation,[],[f37])).
% 2.21/0.64  fof(f1594,plain,(
% 2.21/0.64    spl2_49 | ~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_45),
% 2.21/0.64    inference(avatar_split_clause,[],[f1504,f1486,f189,f78,f73,f1591])).
% 2.21/0.64  fof(f189,plain,(
% 2.21/0.64    spl2_14 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.21/0.64  fof(f1486,plain,(
% 2.21/0.64    spl2_45 <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 2.21/0.64  fof(f1504,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_45)),
% 2.21/0.64    inference(forward_demodulation,[],[f1494,f191])).
% 2.21/0.64  fof(f191,plain,(
% 2.21/0.64    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_14),
% 2.21/0.64    inference(avatar_component_clause,[],[f189])).
% 2.21/0.64  fof(f1494,plain,(
% 2.21/0.64    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK1)))) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_45)),
% 2.21/0.64    inference(superposition,[],[f931,f1488])).
% 2.21/0.64  fof(f1488,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_45),
% 2.21/0.64    inference(avatar_component_clause,[],[f1486])).
% 2.21/0.64  fof(f931,plain,(
% 2.21/0.64    ( ! [X1] : (k10_relat_1(sK1,k6_subset_1(k1_xboole_0,X1)) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_14)),
% 2.21/0.64    inference(superposition,[],[f922,f191])).
% 2.21/0.64  fof(f1535,plain,(
% 2.21/0.64    spl2_48 | ~spl2_45),
% 2.21/0.64    inference(avatar_split_clause,[],[f1506,f1486,f1532])).
% 2.21/0.64  fof(f1506,plain,(
% 2.21/0.64    r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_45),
% 2.21/0.64    inference(subsumption_resolution,[],[f1496,f65])).
% 2.21/0.64  fof(f1496,plain,(
% 2.21/0.64    k1_xboole_0 != k6_subset_1(k1_xboole_0,k1_xboole_0) | r1_tarski(k10_relat_1(sK1,k1_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_45),
% 2.21/0.64    inference(superposition,[],[f423,f1488])).
% 2.21/0.64  fof(f423,plain,(
% 2.21/0.64    ( ! [X1] : (k1_xboole_0 != k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X1)) | r1_tarski(X1,X1)) )),
% 2.21/0.64    inference(forward_demodulation,[],[f421,f67])).
% 2.21/0.64  fof(f421,plain,(
% 2.21/0.64    ( ! [X1] : (k1_xboole_0 != k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) | r1_tarski(X1,X1)) )),
% 2.21/0.64    inference(superposition,[],[f71,f398])).
% 2.21/0.64  fof(f398,plain,(
% 2.21/0.64    ( ! [X0] : (k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k6_subset_1(X0,X0)) )),
% 2.21/0.64    inference(superposition,[],[f394,f65])).
% 2.21/0.64  fof(f1520,plain,(
% 2.21/0.64    spl2_47 | ~spl2_45),
% 2.21/0.64    inference(avatar_split_clause,[],[f1492,f1486,f1517])).
% 2.21/0.64  fof(f1517,plain,(
% 2.21/0.64    spl2_47 <=> r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 2.21/0.64  fof(f1492,plain,(
% 2.21/0.64    r1_xboole_0(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_45),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1488,f68])).
% 2.21/0.64  fof(f1515,plain,(
% 2.21/0.64    spl2_46 | ~spl2_45),
% 2.21/0.64    inference(avatar_split_clause,[],[f1490,f1486,f1512])).
% 2.21/0.64  fof(f1512,plain,(
% 2.21/0.64    spl2_46 <=> r1_tarski(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 2.21/0.64  fof(f1490,plain,(
% 2.21/0.64    r1_tarski(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_45),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1488,f71])).
% 2.21/0.64  fof(f1489,plain,(
% 2.21/0.64    spl2_45 | ~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_16),
% 2.21/0.64    inference(avatar_split_clause,[],[f1456,f210,f189,f78,f73,f1486])).
% 2.21/0.64  fof(f210,plain,(
% 2.21/0.64    spl2_16 <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.21/0.64  fof(f1456,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_16)),
% 2.21/0.64    inference(forward_demodulation,[],[f1428,f191])).
% 2.21/0.64  fof(f1428,plain,(
% 2.21/0.64    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,k1_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_16)),
% 2.21/0.64    inference(superposition,[],[f931,f212])).
% 2.21/0.64  fof(f212,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_relat_1(sK1)) | ~spl2_16),
% 2.21/0.64    inference(avatar_component_clause,[],[f210])).
% 2.21/0.64  fof(f1426,plain,(
% 2.21/0.64    spl2_44 | ~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_30 | ~spl2_37),
% 2.21/0.64    inference(avatar_split_clause,[],[f1377,f802,f610,f134,f78,f73,f1423])).
% 2.21/0.64  fof(f1423,plain,(
% 2.21/0.64    spl2_44 <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 2.21/0.64  fof(f610,plain,(
% 2.21/0.64    spl2_30 <=> k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 2.21/0.64  fof(f802,plain,(
% 2.21/0.64    spl2_37 <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 2.21/0.64  fof(f1377,plain,(
% 2.21/0.64    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_30 | ~spl2_37)),
% 2.21/0.64    inference(backward_demodulation,[],[f804,f1370])).
% 2.21/0.64  fof(f1370,plain,(
% 2.21/0.64    ( ! [X0] : (k2_relat_1(sK1) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_30)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1285,f69])).
% 2.21/0.64  fof(f1285,plain,(
% 2.21/0.64    ( ! [X0] : (r1_xboole_0(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_30)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f955,f51])).
% 2.21/0.64  fof(f955,plain,(
% 2.21/0.64    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k1_relat_1(sK1))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_30)),
% 2.21/0.64    inference(forward_demodulation,[],[f935,f146])).
% 2.21/0.64  fof(f146,plain,(
% 2.21/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f143,f70])).
% 2.21/0.64  fof(f935,plain,(
% 2.21/0.64    ( ! [X2] : (k6_subset_1(k10_relat_1(sK1,X2),k1_relat_1(sK1)) = k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k1_relat_1(sK1))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_30)),
% 2.21/0.64    inference(superposition,[],[f922,f612])).
% 2.21/0.64  fof(f612,plain,(
% 2.21/0.64    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_30),
% 2.21/0.64    inference(avatar_component_clause,[],[f610])).
% 2.21/0.64  fof(f804,plain,(
% 2.21/0.64    k9_relat_1(sK1,k1_relat_1(sK1)) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_37),
% 2.21/0.64    inference(avatar_component_clause,[],[f802])).
% 2.21/0.64  fof(f1233,plain,(
% 2.21/0.64    spl2_42 | ~spl2_43 | ~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22),
% 2.21/0.64    inference(avatar_split_clause,[],[f1069,f299,f134,f78,f73,f1230,f1226])).
% 2.21/0.64  fof(f1226,plain,(
% 2.21/0.64    spl2_42 <=> r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 2.21/0.64  fof(f1230,plain,(
% 2.21/0.64    spl2_43 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 2.21/0.64  fof(f299,plain,(
% 2.21/0.64    spl2_22 <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 2.21/0.64  fof(f1069,plain,(
% 2.21/0.64    k1_xboole_0 != k2_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22)),
% 2.21/0.64    inference(superposition,[],[f424,f1002])).
% 2.21/0.64  fof(f1002,plain,(
% 2.21/0.64    ( ! [X5] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(X5,k2_relat_1(sK1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22)),
% 2.21/0.64    inference(forward_demodulation,[],[f976,f301])).
% 2.21/0.64  fof(f301,plain,(
% 2.21/0.64    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) | ~spl2_22),
% 2.21/0.64    inference(avatar_component_clause,[],[f299])).
% 2.21/0.64  fof(f976,plain,(
% 2.21/0.64    ( ! [X5] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k6_subset_1(X5,k2_relat_1(sK1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f239,f953])).
% 2.21/0.64  fof(f953,plain,(
% 2.21/0.64    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.21/0.64    inference(forward_demodulation,[],[f933,f146])).
% 2.21/0.64  fof(f933,plain,(
% 2.21/0.64    ( ! [X0] : (k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f922,f136])).
% 2.21/0.64  fof(f424,plain,(
% 2.21/0.64    ( ! [X2] : (k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X2)) != X2 | r1_xboole_0(X2,X2)) )),
% 2.21/0.64    inference(forward_demodulation,[],[f422,f67])).
% 2.21/0.64  fof(f422,plain,(
% 2.21/0.64    ( ! [X2] : (k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) != X2 | r1_xboole_0(X2,X2)) )),
% 2.21/0.64    inference(superposition,[],[f68,f398])).
% 2.21/0.64  fof(f1109,plain,(
% 2.21/0.64    spl2_41 | ~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22),
% 2.21/0.64    inference(avatar_split_clause,[],[f1068,f299,f134,f78,f73,f1106])).
% 2.21/0.64  fof(f1106,plain,(
% 2.21/0.64    spl2_41 <=> k1_xboole_0 = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 2.21/0.64  fof(f1068,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22)),
% 2.21/0.64    inference(superposition,[],[f1002,f416])).
% 2.21/0.64  fof(f416,plain,(
% 2.21/0.64    ( ! [X4] : (k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X4)) = k6_subset_1(X4,X4)) )),
% 2.21/0.64    inference(superposition,[],[f398,f67])).
% 2.21/0.64  fof(f1100,plain,(
% 2.21/0.64    spl2_40 | ~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22),
% 2.21/0.64    inference(avatar_split_clause,[],[f1088,f299,f134,f78,f73,f1097])).
% 2.21/0.64  fof(f1097,plain,(
% 2.21/0.64    spl2_40 <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 2.21/0.64  fof(f1088,plain,(
% 2.21/0.64    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22)),
% 2.21/0.64    inference(forward_demodulation,[],[f1061,f65])).
% 2.21/0.64  fof(f1061,plain,(
% 2.21/0.64    r1_tarski(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k1_xboole_0)) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_22)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f1002,f411])).
% 2.21/0.64  fof(f411,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,k6_subset_1(X1,X0)) | r1_tarski(X0,k6_subset_1(X0,X1))) )),
% 2.21/0.64    inference(forward_demodulation,[],[f404,f67])).
% 2.21/0.64  fof(f404,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) | r1_tarski(X0,k6_subset_1(X0,X1))) )),
% 2.21/0.64    inference(superposition,[],[f71,f394])).
% 2.21/0.64  fof(f856,plain,(
% 2.21/0.64    spl2_39 | ~spl2_38),
% 2.21/0.64    inference(avatar_split_clause,[],[f827,f818,f853])).
% 2.21/0.64  fof(f853,plain,(
% 2.21/0.64    spl2_39 <=> k1_xboole_0 = k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 2.21/0.64  fof(f818,plain,(
% 2.21/0.64    spl2_38 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 2.21/0.64  fof(f827,plain,(
% 2.21/0.64    k1_xboole_0 = k1_setfam_1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))) | ~spl2_38),
% 2.21/0.64    inference(superposition,[],[f820,f398])).
% 2.21/0.64  fof(f820,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_38),
% 2.21/0.64    inference(avatar_component_clause,[],[f818])).
% 2.21/0.64  fof(f821,plain,(
% 2.21/0.64    spl2_38 | ~spl2_36),
% 2.21/0.64    inference(avatar_split_clause,[],[f724,f719,f818])).
% 2.21/0.64  fof(f719,plain,(
% 2.21/0.64    spl2_36 <=> r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 2.21/0.64  fof(f724,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_36),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f721,f70])).
% 2.21/0.64  fof(f721,plain,(
% 2.21/0.64    r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_36),
% 2.21/0.64    inference(avatar_component_clause,[],[f719])).
% 2.21/0.64  fof(f805,plain,(
% 2.21/0.64    spl2_37 | ~spl2_23),
% 2.21/0.64    inference(avatar_split_clause,[],[f498,f319,f802])).
% 2.21/0.64  fof(f319,plain,(
% 2.21/0.64    spl2_23 <=> k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.21/0.64  fof(f498,plain,(
% 2.21/0.64    k9_relat_1(sK1,k1_relat_1(sK1)) = k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_23),
% 2.21/0.64    inference(forward_demodulation,[],[f471,f65])).
% 2.21/0.64  fof(f471,plain,(
% 2.21/0.64    k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))) = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k1_xboole_0) | ~spl2_23),
% 2.21/0.64    inference(superposition,[],[f403,f321])).
% 2.21/0.64  fof(f321,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) | ~spl2_23),
% 2.21/0.64    inference(avatar_component_clause,[],[f319])).
% 2.21/0.64  fof(f722,plain,(
% 2.21/0.64    spl2_36 | ~spl2_35),
% 2.21/0.64    inference(avatar_split_clause,[],[f704,f678,f719])).
% 2.21/0.64  fof(f678,plain,(
% 2.21/0.64    spl2_35 <=> k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 2.21/0.64  fof(f704,plain,(
% 2.21/0.64    r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_35),
% 2.21/0.64    inference(subsumption_resolution,[],[f690,f65])).
% 2.21/0.64  fof(f690,plain,(
% 2.21/0.64    k1_xboole_0 != k6_subset_1(k1_xboole_0,k1_xboole_0) | r1_tarski(k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))),k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_35),
% 2.21/0.64    inference(superposition,[],[f423,f680])).
% 2.21/0.64  fof(f680,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_35),
% 2.21/0.64    inference(avatar_component_clause,[],[f678])).
% 2.21/0.64  fof(f681,plain,(
% 2.21/0.64    spl2_35 | ~spl2_32),
% 2.21/0.64    inference(avatar_split_clause,[],[f644,f636,f678])).
% 2.21/0.64  fof(f636,plain,(
% 2.21/0.64    spl2_32 <=> k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 2.21/0.64  fof(f644,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_32),
% 2.21/0.64    inference(superposition,[],[f638,f416])).
% 2.21/0.64  fof(f638,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_32),
% 2.21/0.64    inference(avatar_component_clause,[],[f636])).
% 2.21/0.64  fof(f666,plain,(
% 2.21/0.64    spl2_34 | ~spl2_32),
% 2.21/0.64    inference(avatar_split_clause,[],[f642,f636,f663])).
% 2.21/0.64  fof(f663,plain,(
% 2.21/0.64    spl2_34 <=> r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 2.21/0.64  fof(f642,plain,(
% 2.21/0.64    r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_32),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f638,f429])).
% 2.21/0.64  fof(f429,plain,(
% 2.21/0.64    ( ! [X2] : (k1_xboole_0 != k6_subset_1(X2,X2) | r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,X2))) )),
% 2.21/0.64    inference(superposition,[],[f71,f416])).
% 2.21/0.64  fof(f661,plain,(
% 2.21/0.64    spl2_33 | ~spl2_32),
% 2.21/0.64    inference(avatar_split_clause,[],[f641,f636,f658])).
% 2.21/0.64  fof(f658,plain,(
% 2.21/0.64    spl2_33 <=> r1_xboole_0(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 2.21/0.64  fof(f641,plain,(
% 2.21/0.64    r1_xboole_0(k1_xboole_0,k6_subset_1(k1_xboole_0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_32),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f638,f430])).
% 2.21/0.64  fof(f430,plain,(
% 2.21/0.64    ( ! [X3] : (k1_xboole_0 != k6_subset_1(X3,X3) | r1_xboole_0(k1_xboole_0,k6_subset_1(k1_xboole_0,X3))) )),
% 2.21/0.64    inference(superposition,[],[f68,f416])).
% 2.21/0.64  fof(f639,plain,(
% 2.21/0.64    spl2_32 | ~spl2_1 | ~spl2_2 | ~spl2_30),
% 2.21/0.64    inference(avatar_split_clause,[],[f619,f610,f78,f73,f636])).
% 2.21/0.64  fof(f619,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_30)),
% 2.21/0.64    inference(superposition,[],[f239,f612])).
% 2.21/0.64  fof(f631,plain,(
% 2.21/0.64    spl2_31 | ~spl2_1 | ~spl2_2 | ~spl2_30),
% 2.21/0.64    inference(avatar_split_clause,[],[f618,f610,f78,f73,f628])).
% 2.21/0.64  fof(f628,plain,(
% 2.21/0.64    spl2_31 <=> r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.21/0.64  fof(f618,plain,(
% 2.21/0.64    r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_30)),
% 2.21/0.64    inference(superposition,[],[f235,f612])).
% 2.21/0.64  fof(f613,plain,(
% 2.21/0.64    spl2_30 | ~spl2_1 | ~spl2_9 | ~spl2_25),
% 2.21/0.64    inference(avatar_split_clause,[],[f604,f363,f134,f73,f610])).
% 2.21/0.64  fof(f363,plain,(
% 2.21/0.64    spl2_25 <=> k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 2.21/0.64  fof(f604,plain,(
% 2.21/0.64    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) | (~spl2_1 | ~spl2_9 | ~spl2_25)),
% 2.21/0.64    inference(forward_demodulation,[],[f592,f65])).
% 2.21/0.64  fof(f592,plain,(
% 2.21/0.64    k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k6_subset_1(k1_relat_1(sK1),k1_xboole_0) | (~spl2_1 | ~spl2_9 | ~spl2_25)),
% 2.21/0.64    inference(superposition,[],[f496,f365])).
% 2.21/0.64  fof(f365,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_25),
% 2.21/0.64    inference(avatar_component_clause,[],[f363])).
% 2.21/0.64  fof(f496,plain,(
% 2.21/0.64    ( ! [X10] : (k10_relat_1(sK1,X10) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X10)))) ) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(forward_demodulation,[],[f469,f65])).
% 2.21/0.64  fof(f469,plain,(
% 2.21/0.64    ( ! [X10] : (k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X10))) = k6_subset_1(k10_relat_1(sK1,X10),k1_xboole_0)) ) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f403,f146])).
% 2.21/0.64  fof(f588,plain,(
% 2.21/0.64    spl2_28 | ~spl2_29 | ~spl2_5),
% 2.21/0.64    inference(avatar_split_clause,[],[f577,f100,f585,f581])).
% 2.21/0.64  fof(f581,plain,(
% 2.21/0.64    spl2_28 <=> r1_xboole_0(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.21/0.64  fof(f585,plain,(
% 2.21/0.64    spl2_29 <=> sK0 = k2_relat_1(sK1)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 2.21/0.64  fof(f100,plain,(
% 2.21/0.64    spl2_5 <=> k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.21/0.64  fof(f577,plain,(
% 2.21/0.64    sK0 != k2_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0)) | ~spl2_5),
% 2.21/0.64    inference(forward_demodulation,[],[f563,f65])).
% 2.21/0.64  fof(f563,plain,(
% 2.21/0.64    k2_relat_1(sK1) != k6_subset_1(sK0,k1_xboole_0) | r1_xboole_0(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0)) | ~spl2_5),
% 2.21/0.64    inference(superposition,[],[f412,f102])).
% 2.21/0.64  fof(f102,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) | ~spl2_5),
% 2.21/0.64    inference(avatar_component_clause,[],[f100])).
% 2.21/0.64  fof(f412,plain,(
% 2.21/0.64    ( ! [X2,X3] : (k6_subset_1(X3,k6_subset_1(X3,X2)) != X2 | r1_xboole_0(X2,k6_subset_1(X2,X3))) )),
% 2.21/0.64    inference(forward_demodulation,[],[f405,f67])).
% 2.21/0.64  fof(f405,plain,(
% 2.21/0.64    ( ! [X2,X3] : (k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X2)) != X2 | r1_xboole_0(X2,k6_subset_1(X2,X3))) )),
% 2.21/0.64    inference(superposition,[],[f68,f394])).
% 2.21/0.64  fof(f391,plain,(
% 2.21/0.64    spl2_26 | ~spl2_27 | ~spl2_23),
% 2.21/0.64    inference(avatar_split_clause,[],[f326,f319,f388,f384])).
% 2.21/0.64  fof(f384,plain,(
% 2.21/0.64    spl2_26 <=> r1_xboole_0(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 2.21/0.64  fof(f388,plain,(
% 2.21/0.64    spl2_27 <=> k1_xboole_0 = k9_relat_1(sK1,k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.21/0.64  fof(f326,plain,(
% 2.21/0.64    k1_xboole_0 != k9_relat_1(sK1,k1_relat_1(sK1)) | r1_xboole_0(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) | ~spl2_23),
% 2.21/0.64    inference(superposition,[],[f68,f321])).
% 2.21/0.64  fof(f366,plain,(
% 2.21/0.64    spl2_25 | ~spl2_24),
% 2.21/0.64    inference(avatar_split_clause,[],[f353,f348,f363])).
% 2.21/0.64  fof(f348,plain,(
% 2.21/0.64    spl2_24 <=> r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 2.21/0.64  fof(f353,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_24),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f350,f70])).
% 2.21/0.64  fof(f350,plain,(
% 2.21/0.64    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~spl2_24),
% 2.21/0.64    inference(avatar_component_clause,[],[f348])).
% 2.21/0.64  fof(f351,plain,(
% 2.21/0.64    spl2_24 | ~spl2_1 | ~spl2_10),
% 2.21/0.64    inference(avatar_split_clause,[],[f336,f150,f73,f348])).
% 2.21/0.64  fof(f150,plain,(
% 2.21/0.64    spl2_10 <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.21/0.64  fof(f336,plain,(
% 2.21/0.64    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) | (~spl2_1 | ~spl2_10)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f152,f50])).
% 2.21/0.64  fof(f152,plain,(
% 2.21/0.64    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_10),
% 2.21/0.64    inference(avatar_component_clause,[],[f150])).
% 2.21/0.64  fof(f322,plain,(
% 2.21/0.64    spl2_23 | ~spl2_20),
% 2.21/0.64    inference(avatar_split_clause,[],[f274,f269,f319])).
% 2.21/0.64  fof(f269,plain,(
% 2.21/0.64    spl2_20 <=> r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.21/0.64  fof(f274,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) | ~spl2_20),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f271,f70])).
% 2.21/0.64  fof(f271,plain,(
% 2.21/0.64    r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) | ~spl2_20),
% 2.21/0.64    inference(avatar_component_clause,[],[f269])).
% 2.21/0.64  fof(f302,plain,(
% 2.21/0.64    spl2_22 | ~spl2_21),
% 2.21/0.64    inference(avatar_split_clause,[],[f283,f277,f299])).
% 2.21/0.64  fof(f277,plain,(
% 2.21/0.64    spl2_21 <=> k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 2.21/0.64  fof(f283,plain,(
% 2.21/0.64    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) | ~spl2_21),
% 2.21/0.64    inference(superposition,[],[f279,f65])).
% 2.21/0.64  fof(f279,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0) | ~spl2_21),
% 2.21/0.64    inference(avatar_component_clause,[],[f277])).
% 2.21/0.64  fof(f280,plain,(
% 2.21/0.64    spl2_21 | ~spl2_18),
% 2.21/0.64    inference(avatar_split_clause,[],[f256,f249,f277])).
% 2.21/0.64  fof(f249,plain,(
% 2.21/0.64    spl2_18 <=> r1_tarski(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.21/0.64  fof(f256,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0) | ~spl2_18),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f251,f70])).
% 2.21/0.64  fof(f251,plain,(
% 2.21/0.64    r1_tarski(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0) | ~spl2_18),
% 2.21/0.64    inference(avatar_component_clause,[],[f249])).
% 2.21/0.64  fof(f272,plain,(
% 2.21/0.64    spl2_20 | ~spl2_1 | ~spl2_2 | ~spl2_9),
% 2.21/0.64    inference(avatar_split_clause,[],[f243,f134,f78,f73,f269])).
% 2.21/0.64  fof(f243,plain,(
% 2.21/0.64    r1_tarski(k9_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f235,f136])).
% 2.21/0.64  fof(f263,plain,(
% 2.21/0.64    spl2_19 | ~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_17),
% 2.21/0.64    inference(avatar_split_clause,[],[f245,f223,f189,f78,f73,f260])).
% 2.21/0.64  fof(f260,plain,(
% 2.21/0.64    spl2_19 <=> r1_xboole_0(k9_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.21/0.64  fof(f223,plain,(
% 2.21/0.64    spl2_17 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.21/0.64  fof(f245,plain,(
% 2.21/0.64    r1_xboole_0(k9_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_17)),
% 2.21/0.64    inference(forward_demodulation,[],[f240,f191])).
% 2.21/0.64  fof(f240,plain,(
% 2.21/0.64    r1_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_17)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f235,f229])).
% 2.21/0.64  fof(f229,plain,(
% 2.21/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | r1_xboole_0(X0,k1_relat_1(sK1))) ) | ~spl2_17),
% 2.21/0.64    inference(resolution,[],[f225,f60])).
% 2.21/0.64  fof(f225,plain,(
% 2.21/0.64    r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) | ~spl2_17),
% 2.21/0.64    inference(avatar_component_clause,[],[f223])).
% 2.21/0.64  fof(f252,plain,(
% 2.21/0.64    spl2_18 | ~spl2_1 | ~spl2_2 | ~spl2_14),
% 2.21/0.64    inference(avatar_split_clause,[],[f244,f189,f78,f73,f249])).
% 2.21/0.64  fof(f244,plain,(
% 2.21/0.64    r1_tarski(k9_relat_1(sK1,k1_xboole_0),k1_xboole_0) | (~spl2_1 | ~spl2_2 | ~spl2_14)),
% 2.21/0.64    inference(superposition,[],[f235,f191])).
% 2.21/0.64  fof(f226,plain,(
% 2.21/0.64    spl2_17 | ~spl2_16),
% 2.21/0.64    inference(avatar_split_clause,[],[f216,f210,f223])).
% 2.21/0.64  fof(f216,plain,(
% 2.21/0.64    r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) | ~spl2_16),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f212,f68])).
% 2.21/0.64  fof(f213,plain,(
% 2.21/0.64    spl2_16 | ~spl2_1 | ~spl2_9 | ~spl2_14),
% 2.21/0.64    inference(avatar_split_clause,[],[f197,f189,f134,f73,f210])).
% 2.21/0.64  fof(f197,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_relat_1(sK1)) | (~spl2_1 | ~spl2_9 | ~spl2_14)),
% 2.21/0.64    inference(superposition,[],[f146,f191])).
% 2.21/0.64  fof(f205,plain,(
% 2.21/0.64    spl2_15 | ~spl2_1 | ~spl2_9 | ~spl2_14),
% 2.21/0.64    inference(avatar_split_clause,[],[f198,f189,f134,f73,f202])).
% 2.21/0.64  fof(f202,plain,(
% 2.21/0.64    spl2_15 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.21/0.64  fof(f198,plain,(
% 2.21/0.64    r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | (~spl2_1 | ~spl2_9 | ~spl2_14)),
% 2.21/0.64    inference(superposition,[],[f143,f191])).
% 2.21/0.64  fof(f192,plain,(
% 2.21/0.64    spl2_14 | ~spl2_1),
% 2.21/0.64    inference(avatar_split_clause,[],[f186,f73,f189])).
% 2.21/0.64  fof(f186,plain,(
% 2.21/0.64    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_1),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f92,f52])).
% 2.21/0.64  fof(f52,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f35])).
% 2.21/0.64  fof(f92,plain,(
% 2.21/0.64    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f65,f68])).
% 2.21/0.64  fof(f183,plain,(
% 2.21/0.64    spl2_12 | ~spl2_13 | ~spl2_11),
% 2.21/0.64    inference(avatar_split_clause,[],[f165,f158,f180,f176])).
% 2.21/0.64  fof(f176,plain,(
% 2.21/0.64    spl2_12 <=> r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.21/0.64  fof(f180,plain,(
% 2.21/0.64    spl2_13 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.21/0.64  fof(f158,plain,(
% 2.21/0.64    spl2_11 <=> k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.21/0.64  fof(f165,plain,(
% 2.21/0.64    k1_xboole_0 != k1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_11),
% 2.21/0.64    inference(superposition,[],[f68,f160])).
% 2.21/0.64  fof(f160,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_11),
% 2.21/0.64    inference(avatar_component_clause,[],[f158])).
% 2.21/0.64  fof(f161,plain,(
% 2.21/0.64    spl2_11 | ~spl2_10),
% 2.21/0.64    inference(avatar_split_clause,[],[f155,f150,f158])).
% 2.21/0.64  fof(f155,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_10),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f152,f70])).
% 2.21/0.64  fof(f153,plain,(
% 2.21/0.64    spl2_10 | ~spl2_1 | ~spl2_9),
% 2.21/0.64    inference(avatar_split_clause,[],[f148,f134,f73,f150])).
% 2.21/0.64  fof(f148,plain,(
% 2.21/0.64    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_9)),
% 2.21/0.64    inference(superposition,[],[f143,f136])).
% 2.21/0.64  fof(f137,plain,(
% 2.21/0.64    spl2_9 | ~spl2_1),
% 2.21/0.64    inference(avatar_split_clause,[],[f131,f73,f134])).
% 2.21/0.64  fof(f131,plain,(
% 2.21/0.64    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) | ~spl2_1),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f75,f43])).
% 2.21/0.64  fof(f43,plain,(
% 2.21/0.64    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f22])).
% 2.21/0.64  fof(f22,plain,(
% 2.21/0.64    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.64    inference(ennf_transformation,[],[f12])).
% 2.21/0.64  fof(f12,axiom,(
% 2.21/0.64    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.21/0.64  fof(f123,plain,(
% 2.21/0.64    spl2_8),
% 2.21/0.64    inference(avatar_split_clause,[],[f115,f120])).
% 2.21/0.64  fof(f120,plain,(
% 2.21/0.64    spl2_8 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.21/0.64  fof(f115,plain,(
% 2.21/0.64    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f65,f71])).
% 2.21/0.64  fof(f113,plain,(
% 2.21/0.64    spl2_6 | ~spl2_7 | ~spl2_5),
% 2.21/0.64    inference(avatar_split_clause,[],[f104,f100,f110,f106])).
% 2.21/0.64  fof(f106,plain,(
% 2.21/0.64    spl2_6 <=> r1_xboole_0(sK0,k2_relat_1(sK1))),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.21/0.64  fof(f110,plain,(
% 2.21/0.64    spl2_7 <=> k1_xboole_0 = sK0),
% 2.21/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.21/0.64  fof(f104,plain,(
% 2.21/0.64    k1_xboole_0 != sK0 | r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_5),
% 2.21/0.64    inference(superposition,[],[f68,f102])).
% 2.21/0.64  fof(f103,plain,(
% 2.21/0.64    spl2_5 | ~spl2_3),
% 2.21/0.64    inference(avatar_split_clause,[],[f97,f83,f100])).
% 2.21/0.64  fof(f97,plain,(
% 2.21/0.64    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f85,f70])).
% 2.21/0.64  fof(f91,plain,(
% 2.21/0.64    ~spl2_4),
% 2.21/0.64    inference(avatar_split_clause,[],[f41,f88])).
% 2.21/0.64  fof(f41,plain,(
% 2.21/0.64    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 2.21/0.64    inference(cnf_transformation,[],[f34])).
% 2.21/0.64  fof(f34,plain,(
% 2.21/0.64    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.21/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33])).
% 2.21/0.64  fof(f33,plain,(
% 2.21/0.64    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.21/0.64    introduced(choice_axiom,[])).
% 2.21/0.64  fof(f21,plain,(
% 2.21/0.64    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.21/0.64    inference(flattening,[],[f20])).
% 2.21/0.64  fof(f20,plain,(
% 2.21/0.64    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.21/0.64    inference(ennf_transformation,[],[f19])).
% 2.21/0.64  fof(f19,negated_conjecture,(
% 2.21/0.64    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.21/0.64    inference(negated_conjecture,[],[f18])).
% 2.21/0.64  fof(f18,conjecture,(
% 2.21/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 2.21/0.64  fof(f86,plain,(
% 2.21/0.64    spl2_3),
% 2.21/0.64    inference(avatar_split_clause,[],[f40,f83])).
% 2.21/0.64  fof(f40,plain,(
% 2.21/0.64    r1_tarski(sK0,k2_relat_1(sK1))),
% 2.21/0.64    inference(cnf_transformation,[],[f34])).
% 2.21/0.64  fof(f81,plain,(
% 2.21/0.64    spl2_2),
% 2.21/0.64    inference(avatar_split_clause,[],[f39,f78])).
% 2.21/0.64  fof(f39,plain,(
% 2.21/0.64    v1_funct_1(sK1)),
% 2.21/0.64    inference(cnf_transformation,[],[f34])).
% 2.21/0.64  fof(f76,plain,(
% 2.21/0.64    spl2_1),
% 2.21/0.64    inference(avatar_split_clause,[],[f38,f73])).
% 2.21/0.64  fof(f38,plain,(
% 2.21/0.64    v1_relat_1(sK1)),
% 2.21/0.64    inference(cnf_transformation,[],[f34])).
% 2.21/0.64  % SZS output end Proof for theBenchmark
% 2.21/0.64  % (26203)------------------------------
% 2.21/0.64  % (26203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.64  % (26203)Termination reason: Refutation
% 2.21/0.64  
% 2.21/0.64  % (26203)Memory used [KB]: 7291
% 2.21/0.64  % (26203)Time elapsed: 0.237 s
% 2.21/0.64  % (26203)------------------------------
% 2.21/0.64  % (26203)------------------------------
% 2.21/0.64  % (26194)Success in time 0.291 s
%------------------------------------------------------------------------------
