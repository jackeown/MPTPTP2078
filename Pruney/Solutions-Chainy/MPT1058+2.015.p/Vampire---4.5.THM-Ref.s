%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:19 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  238 (1571 expanded)
%              Number of leaves         :   48 ( 575 expanded)
%              Depth                    :   17
%              Number of atoms          :  550 (2386 expanded)
%              Number of equality atoms :  173 (1399 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f98,f102,f106,f123,f154,f165,f172,f189,f196,f204,f255,f259,f309,f311,f317,f363,f468,f655,f977,f1051,f1211,f1282,f1441,f1462,f1463,f1468,f1473,f1477,f1486])).

fof(f1486,plain,
    ( spl5_27
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1482,f1439,f1484])).

fof(f1484,plain,
    ( spl5_27
  <=> k1_xboole_0 = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1439,plain,
    ( spl5_23
  <=> k10_relat_1(sK0,sK2) = k6_subset_1(sK1,k6_subset_1(sK1,k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1482,plain,
    ( k1_xboole_0 = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f1481,f145])).

fof(f145,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f143,f81])).

fof(f81,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f143,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(superposition,[],[f84,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f84,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f66,f79,f63,f63])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1481,plain,
    ( k6_subset_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2)),k6_subset_1(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f1459,f1249])).

fof(f1249,plain,(
    ! [X2,X3] : k6_subset_1(X2,X3) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2) ),
    inference(forward_demodulation,[],[f1248,f125])).

fof(f125,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f124,f51])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f124,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f119,f52])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f1248,plain,(
    ! [X2,X3] : k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),k6_subset_1(X2,X3)) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2) ),
    inference(forward_demodulation,[],[f1247,f125])).

fof(f1247,plain,(
    ! [X2,X3] : k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),k6_subset_1(X2,k10_relat_1(k6_relat_1(X3),X3))) ),
    inference(forward_demodulation,[],[f1214,f399])).

fof(f399,plain,(
    ! [X6,X8,X7] : k6_subset_1(X6,k10_relat_1(k6_relat_1(X7),X8)) = k6_subset_1(X6,k10_relat_1(k7_relat_1(k6_relat_1(X7),X6),X8)) ),
    inference(superposition,[],[f107,f179])).

fof(f179,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k6_subset_1(X3,k6_subset_1(X3,k10_relat_1(k6_relat_1(X2),X4))) ),
    inference(resolution,[],[f109,f49])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) ) ),
    inference(forward_demodulation,[],[f87,f84])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f107,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(forward_demodulation,[],[f85,f84])).

fof(f85,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f63,f63,f79])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1214,plain,(
    ! [X2,X3] : k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),k6_subset_1(X2,k10_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3))) ),
    inference(superposition,[],[f389,f391])).

fof(f391,plain,(
    ! [X0,X1] : k6_subset_1(X1,k6_subset_1(X1,X0)) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f179,f125])).

fof(f389,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) ),
    inference(forward_demodulation,[],[f381,f84])).

fof(f381,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k6_relat_1(X4),k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) ),
    inference(superposition,[],[f177,f141])).

fof(f141,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f84,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f62,f78,f78])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f177,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),k6_subset_1(X1,k6_subset_1(X1,X2))) ),
    inference(forward_demodulation,[],[f176,f52])).

fof(f176,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),k6_subset_1(k2_relat_1(k6_relat_1(X1)),k6_subset_1(k2_relat_1(k6_relat_1(X1)),X2))) ),
    inference(resolution,[],[f108,f49])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k6_subset_1(k2_relat_1(X1),k6_subset_1(k2_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f86,f84])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f68,f79])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f1459,plain,
    ( k6_subset_1(k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),sK1),k6_subset_1(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))
    | ~ spl5_23 ),
    inference(superposition,[],[f416,f1440])).

fof(f1440,plain,
    ( k10_relat_1(sK0,sK2) = k6_subset_1(sK1,k6_subset_1(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f1439])).

fof(f416,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k6_subset_1(X1,X0)) = k6_subset_1(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f190,f125])).

fof(f190,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k6_subset_1(X3,X4)) = k6_subset_1(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(global_subsumption,[],[f49,f185])).

fof(f185,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k6_relat_1(X2))
      | k10_relat_1(k6_relat_1(X2),k6_subset_1(X3,X4)) = k6_subset_1(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1477,plain,
    ( spl5_26
    | ~ spl5_9
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1453,f1439,f187,f1475])).

fof(f1475,plain,
    ( spl5_26
  <=> r1_tarski(k10_relat_1(sK0,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f187,plain,
    ( spl5_9
  <=> ! [X1,X0] : k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1453,plain,
    ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK1))
    | ~ spl5_9
    | ~ spl5_23 ),
    inference(superposition,[],[f301,f1440])).

fof(f301,plain,
    ( ! [X12,X13] : r1_tarski(k10_relat_1(sK0,k6_subset_1(X12,X13)),k10_relat_1(sK0,X12))
    | ~ spl5_9 ),
    inference(superposition,[],[f82,f188])).

fof(f188,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f187])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1473,plain,
    ( spl5_25
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1469,f1439,f1471])).

fof(f1471,plain,
    ( spl5_25
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1469,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f1447,f125])).

fof(f1447,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl5_23 ),
    inference(superposition,[],[f389,f1440])).

fof(f1468,plain,
    ( spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1464,f1439,f1466])).

fof(f1466,plain,
    ( spl5_24
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1464,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f1444,f145])).

fof(f1444,plain,
    ( k6_subset_1(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) = k6_subset_1(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_23 ),
    inference(superposition,[],[f340,f1440])).

fof(f340,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X1,k6_subset_1(X1,X0))) ),
    inference(forward_demodulation,[],[f326,f84])).

fof(f326,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f107,f141])).

fof(f1463,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1443,f1439,f96,f100])).

fof(f100,plain,
    ( spl5_3
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f96,plain,
    ( spl5_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1443,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(superposition,[],[f178,f1440])).

fof(f178,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(sK0,X1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f97])).

fof(f97,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1462,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1442,f1439,f96,f100])).

fof(f1442,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(superposition,[],[f1440,f178])).

fof(f1441,plain,
    ( spl5_23
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1428,f104,f1439])).

fof(f104,plain,
    ( spl5_4
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1428,plain,
    ( k10_relat_1(sK0,sK2) = k6_subset_1(sK1,k6_subset_1(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl5_4 ),
    inference(resolution,[],[f1411,f105])).

fof(f105,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1411,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k6_subset_1(X1,k6_subset_1(X1,X2)) = X2 ) ),
    inference(backward_demodulation,[],[f174,f1410])).

fof(f1410,plain,(
    ! [X6,X5] : k6_subset_1(X5,k6_subset_1(X5,X6)) = k9_relat_1(k6_relat_1(X5),k10_relat_1(k6_relat_1(X5),X6)) ),
    inference(forward_demodulation,[],[f1409,f1321])).

fof(f1321,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k7_relat_1(k6_relat_1(X4),X4),X5) ),
    inference(forward_demodulation,[],[f1320,f389])).

fof(f1320,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) = k10_relat_1(k7_relat_1(k6_relat_1(X4),X4),X5) ),
    inference(forward_demodulation,[],[f1319,f179])).

fof(f1319,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) = k6_subset_1(X4,k6_subset_1(X4,k10_relat_1(k6_relat_1(X4),X5))) ),
    inference(forward_demodulation,[],[f1286,f414])).

fof(f414,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1)) = k6_subset_1(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f190,f125])).

fof(f1286,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) = k6_subset_1(X4,k10_relat_1(k6_relat_1(X4),k6_subset_1(X4,X5))) ),
    inference(superposition,[],[f414,f324])).

fof(f324,plain,(
    ! [X4,X3] : k6_subset_1(X3,k6_subset_1(X3,X4)) = k6_subset_1(X4,k6_subset_1(X4,X3)) ),
    inference(superposition,[],[f141,f84])).

fof(f1409,plain,(
    ! [X6,X5] : k6_subset_1(X5,k6_subset_1(X5,X6)) = k9_relat_1(k6_relat_1(X5),k10_relat_1(k7_relat_1(k6_relat_1(X5),X5),X6)) ),
    inference(forward_demodulation,[],[f1401,f179])).

fof(f1401,plain,(
    ! [X6,X5] : k6_subset_1(X5,k6_subset_1(X5,X6)) = k9_relat_1(k6_relat_1(X5),k6_subset_1(X5,k6_subset_1(X5,k10_relat_1(k6_relat_1(X5),X6)))) ),
    inference(superposition,[],[f427,f414])).

fof(f427,plain,(
    ! [X2,X3] : k6_subset_1(X2,X3) = k9_relat_1(k6_relat_1(X2),k6_subset_1(X2,k10_relat_1(k6_relat_1(X2),X3))) ),
    inference(backward_demodulation,[],[f355,f414])).

fof(f355,plain,(
    ! [X2,X3] : k6_subset_1(X2,X3) = k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),k6_subset_1(X2,X3))) ),
    inference(resolution,[],[f174,f82])).

fof(f174,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(global_subsumption,[],[f49,f173])).

fof(f173,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(k6_relat_1(X1))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(forward_demodulation,[],[f168,f52])).

fof(f168,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ r1_tarski(X2,k2_relat_1(k6_relat_1(X1)))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(resolution,[],[f69,f50])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1282,plain,
    ( ~ spl5_22
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1278,f307,f151,f1280])).

fof(f1280,plain,
    ( spl5_22
  <=> r2_hidden(k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f151,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f307,plain,
    ( spl5_14
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1278,plain,
    ( ~ r2_hidden(k1_relat_1(sK0),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(resolution,[],[f1079,f110])).

fof(f110,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f82,f81])).

fof(f1079,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(sK0),X2)
        | ~ r2_hidden(X2,k1_xboole_0) )
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(resolution,[],[f368,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f368,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k1_relat_1(sK0))
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(superposition,[],[f152,f308])).

fof(f308,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f307])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK0,X1))
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1211,plain,
    ( ~ spl5_2
    | ~ spl5_1
    | spl5_21
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f1207,f194,f1209,f92,f96])).

fof(f92,plain,
    ( spl5_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1209,plain,
    ( spl5_21
  <=> ! [X3] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X3)
        | ~ r2_hidden(k1_funct_1(sK0,sK3(sK0,X3,k1_relat_1(sK0))),X3)
        | ~ r2_hidden(sK3(sK0,X3,k1_relat_1(sK0)),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f194,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK0,X0,X1),k1_relat_1(sK0))
        | k10_relat_1(sK0,X0) = X1
        | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1207,plain,
    ( ! [X3] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X3)
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(sK3(sK0,X3,k1_relat_1(sK0)),k1_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(sK0,sK3(sK0,X3,k1_relat_1(sK0))),X3)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f1206])).

fof(f1206,plain,
    ( ! [X3] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X3)
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(sK3(sK0,X3,k1_relat_1(sK0)),k1_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(sK0,sK3(sK0,X3,k1_relat_1(sK0))),X3)
        | ~ v1_relat_1(sK0)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3) )
    | ~ spl5_10 ),
    inference(resolution,[],[f446,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ v1_relat_1(X0)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f446,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0,k1_relat_1(sK0)),k1_relat_1(sK0))
        | k1_relat_1(sK0) = k10_relat_1(sK0,X0) )
    | ~ spl5_10 ),
    inference(factoring,[],[f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1051,plain,
    ( spl5_20
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f1047,f187,f121,f96,f1049])).

fof(f1049,plain,
    ( spl5_20
  <=> k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f121,plain,
    ( spl5_5
  <=> k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1047,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f1046,f122])).

fof(f122,plain,
    ( k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1046,plain,
    ( k10_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f1045,f284])).

fof(f284,plain,
    ( ! [X17] : k10_relat_1(sK0,k10_relat_1(sK0,X17)) = k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),X17))
    | ~ spl5_2 ),
    inference(superposition,[],[f175,f178])).

fof(f175,plain,
    ( ! [X0] : k10_relat_1(sK0,X0) = k10_relat_1(sK0,k6_subset_1(k2_relat_1(sK0),k6_subset_1(k2_relat_1(sK0),X0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f108,f97])).

fof(f1045,plain,
    ( k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f1044,f178])).

fof(f1044,plain,
    ( k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) = k6_subset_1(k1_relat_1(sK0),k6_subset_1(k1_relat_1(sK0),k10_relat_1(sK0,k1_relat_1(sK0))))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f1013,f290])).

fof(f290,plain,
    ( ! [X0] : k10_relat_1(sK0,k6_subset_1(k2_relat_1(sK0),X0)) = k6_subset_1(k1_relat_1(sK0),k10_relat_1(sK0,X0))
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(superposition,[],[f188,f122])).

fof(f1013,plain,
    ( k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) = k6_subset_1(k1_relat_1(sK0),k10_relat_1(sK0,k6_subset_1(k2_relat_1(sK0),k1_relat_1(sK0))))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(superposition,[],[f290,f271])).

fof(f271,plain,
    ( ! [X0] : k10_relat_1(k7_relat_1(sK0,X0),k2_relat_1(sK0)) = k6_subset_1(X0,k6_subset_1(X0,k1_relat_1(sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f178,f122])).

fof(f977,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f962,f121,f96,f975])).

fof(f975,plain,
    ( spl5_19
  <=> k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f962,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f175,f271])).

fof(f655,plain,
    ( spl5_18
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f647,f121,f96,f653])).

fof(f653,plain,
    ( spl5_18
  <=> k1_relat_1(sK0) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f647,plain,
    ( k1_relat_1(sK0) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k2_relat_1(sK0))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f287,f122])).

fof(f287,plain,
    ( ! [X0] : k10_relat_1(sK0,X0) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f273,f81])).

fof(f273,plain,
    ( ! [X0] : k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k6_subset_1(k10_relat_1(sK0,X0),k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f178,f145])).

fof(f468,plain,
    ( ~ spl5_2
    | ~ spl5_1
    | spl5_17
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f451,f202,f466,f92,f96])).

fof(f466,plain,
    ( spl5_17
  <=> ! [X5,X6] :
        ( r2_hidden(sK3(sK0,X5,X6),X6)
        | r2_hidden(sK3(sK0,X5,X6),k10_relat_1(sK0,X5))
        | ~ r2_hidden(sK3(sK0,X5,X6),k1_relat_1(sK0))
        | k10_relat_1(sK0,X5) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f202,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( r2_hidden(k1_funct_1(sK0,sK3(sK0,X0,X1)),X0)
        | k10_relat_1(sK0,X0) = X1
        | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f451,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK3(sK0,X5,X6),X6)
        | k10_relat_1(sK0,X5) = X6
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(sK3(sK0,X5,X6),k1_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | r2_hidden(sK3(sK0,X5,X6),k10_relat_1(sK0,X5)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f203,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK0,sK3(sK0,X0,X1)),X0)
        | r2_hidden(sK3(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f363,plain,
    ( spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f358,f104,f361])).

fof(f361,plain,
    ( spl5_16
  <=> k10_relat_1(sK0,sK2) = k9_relat_1(k6_relat_1(sK1),k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f358,plain,
    ( k10_relat_1(sK0,sK2) = k9_relat_1(k6_relat_1(sK1),k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))
    | ~ spl5_4 ),
    inference(resolution,[],[f174,f105])).

fof(f317,plain,
    ( spl5_15
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f313,f307,f257,f315])).

fof(f315,plain,
    ( spl5_15
  <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f257,plain,
    ( spl5_13
  <=> k1_xboole_0 = k9_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f313,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f258,f308])).

fof(f258,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f311,plain,
    ( spl5_14
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f310,f187,f307])).

fof(f310,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f297,f145])).

fof(f297,plain,
    ( ! [X3] : k1_xboole_0 = k10_relat_1(sK0,k6_subset_1(X3,X3))
    | ~ spl5_9 ),
    inference(superposition,[],[f145,f188])).

fof(f309,plain,
    ( spl5_14
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f305,f187,f307])).

fof(f305,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f294,f145])).

fof(f294,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(sK0,k6_subset_1(X2,X2))
    | ~ spl5_9 ),
    inference(superposition,[],[f188,f145])).

fof(f259,plain,
    ( spl5_13
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f248,f170,f257])).

fof(f170,plain,
    ( spl5_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK0))
        | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f248,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))
    | ~ spl5_8 ),
    inference(resolution,[],[f171,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK0))
        | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f255,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f251,f170,f121,f253])).

fof(f253,plain,
    ( spl5_12
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f251,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f247,f122])).

fof(f247,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))
    | ~ spl5_8 ),
    inference(resolution,[],[f171,f110])).

fof(f204,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f199,f92,f96,f202])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | r2_hidden(k1_funct_1(sK0,sK3(sK0,X0,X1)),X0)
        | r2_hidden(sK3(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl5_1 ),
    inference(resolution,[],[f57,f93])).

fof(f93,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f196,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f191,f92,f96,f194])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | r2_hidden(sK3(sK0,X0,X1),k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f93])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f189,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f184,f92,f96,f187])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f93])).

fof(f172,plain,
    ( spl5_8
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f167,f92,f96,f170])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ r1_tarski(X0,k2_relat_1(sK0))
        | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0 )
    | ~ spl5_1 ),
    inference(resolution,[],[f69,f93])).

fof(f165,plain,
    ( spl5_7
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f160,f92,f96,f163])).

fof(f163,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),X1)
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | r2_hidden(k1_funct_1(sK0,X0),X1)
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f89,f93])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f154,plain,
    ( spl5_6
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f148,f92,f96,f151])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f90,f93])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f118,f96,f121])).

fof(f118,plain,
    ( k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f97])).

fof(f106,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f102,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f43,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:37 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.46  % (15040)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.47  % (15019)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (15041)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (15025)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (15029)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (15034)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (15029)Refutation not found, incomplete strategy% (15029)------------------------------
% 0.21/0.51  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15029)Memory used [KB]: 10618
% 0.21/0.51  % (15029)Time elapsed: 0.101 s
% 0.21/0.51  % (15029)------------------------------
% 0.21/0.51  % (15029)------------------------------
% 0.21/0.51  % (15032)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (15020)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15033)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15023)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15024)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15027)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15022)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (15045)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (15043)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (15041)Refutation not found, incomplete strategy% (15041)------------------------------
% 0.21/0.52  % (15041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15041)Memory used [KB]: 10746
% 0.21/0.52  % (15041)Time elapsed: 0.100 s
% 0.21/0.52  % (15041)------------------------------
% 0.21/0.52  % (15041)------------------------------
% 0.21/0.52  % (15021)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15042)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (15048)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (15037)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15028)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (15035)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15046)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (15038)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15031)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15044)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (15026)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (15030)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (15030)Refutation not found, incomplete strategy% (15030)------------------------------
% 0.21/0.53  % (15030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15030)Memory used [KB]: 10618
% 0.21/0.53  % (15030)Time elapsed: 0.125 s
% 0.21/0.53  % (15030)------------------------------
% 0.21/0.53  % (15030)------------------------------
% 0.21/0.53  % (15047)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (15039)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (15036)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (15036)Refutation not found, incomplete strategy% (15036)------------------------------
% 1.45/0.56  % (15036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (15036)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (15036)Memory used [KB]: 10618
% 1.45/0.56  % (15036)Time elapsed: 0.150 s
% 1.45/0.56  % (15036)------------------------------
% 1.45/0.56  % (15036)------------------------------
% 1.98/0.63  % (15079)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.16/0.65  % (15085)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.16/0.66  % (15090)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.16/0.70  % (15102)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.06/0.81  % (15047)Refutation found. Thanks to Tanya!
% 3.06/0.81  % SZS status Theorem for theBenchmark
% 3.06/0.81  % SZS output start Proof for theBenchmark
% 3.06/0.81  fof(f1487,plain,(
% 3.06/0.81    $false),
% 3.06/0.81    inference(avatar_sat_refutation,[],[f94,f98,f102,f106,f123,f154,f165,f172,f189,f196,f204,f255,f259,f309,f311,f317,f363,f468,f655,f977,f1051,f1211,f1282,f1441,f1462,f1463,f1468,f1473,f1477,f1486])).
% 3.06/0.81  fof(f1486,plain,(
% 3.06/0.81    spl5_27 | ~spl5_23),
% 3.06/0.81    inference(avatar_split_clause,[],[f1482,f1439,f1484])).
% 3.06/0.81  fof(f1484,plain,(
% 3.06/0.81    spl5_27 <=> k1_xboole_0 = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 3.06/0.81  fof(f1439,plain,(
% 3.06/0.81    spl5_23 <=> k10_relat_1(sK0,sK2) = k6_subset_1(sK1,k6_subset_1(sK1,k10_relat_1(sK0,sK2)))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 3.06/0.81  fof(f1482,plain,(
% 3.06/0.81    k1_xboole_0 = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) | ~spl5_23),
% 3.06/0.81    inference(forward_demodulation,[],[f1481,f145])).
% 3.06/0.81  fof(f145,plain,(
% 3.06/0.81    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 3.06/0.81    inference(forward_demodulation,[],[f143,f81])).
% 3.06/0.81  fof(f81,plain,(
% 3.06/0.81    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.06/0.81    inference(definition_unfolding,[],[f48,f63])).
% 3.06/0.81  fof(f63,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f13])).
% 3.06/0.81  fof(f13,axiom,(
% 3.06/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.06/0.81  fof(f48,plain,(
% 3.06/0.81    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.06/0.81    inference(cnf_transformation,[],[f6])).
% 3.06/0.81  fof(f6,axiom,(
% 3.06/0.81    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.06/0.81  fof(f143,plain,(
% 3.06/0.81    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 3.06/0.81    inference(superposition,[],[f84,f80])).
% 3.06/0.81  fof(f80,plain,(
% 3.06/0.81    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 3.06/0.81    inference(definition_unfolding,[],[f47,f79])).
% 3.06/0.81  fof(f79,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.06/0.81    inference(definition_unfolding,[],[f65,f78])).
% 3.06/0.81  fof(f78,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.06/0.81    inference(definition_unfolding,[],[f64,f74])).
% 3.06/0.81  fof(f74,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f12])).
% 3.06/0.81  fof(f12,axiom,(
% 3.06/0.81    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.06/0.81  fof(f64,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f11])).
% 3.06/0.81  fof(f11,axiom,(
% 3.06/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.06/0.81  fof(f65,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f14])).
% 3.06/0.81  fof(f14,axiom,(
% 3.06/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.06/0.81  fof(f47,plain,(
% 3.06/0.81    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f3])).
% 3.06/0.81  fof(f3,axiom,(
% 3.06/0.81    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 3.06/0.81  fof(f84,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.06/0.81    inference(definition_unfolding,[],[f66,f79,f63,f63])).
% 3.06/0.81  fof(f66,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f9])).
% 3.06/0.81  fof(f9,axiom,(
% 3.06/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.06/0.81  fof(f1481,plain,(
% 3.06/0.81    k6_subset_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2)),k6_subset_1(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) | ~spl5_23),
% 3.06/0.81    inference(forward_demodulation,[],[f1459,f1249])).
% 3.06/0.81  fof(f1249,plain,(
% 3.06/0.81    ( ! [X2,X3] : (k6_subset_1(X2,X3) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2)) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1248,f125])).
% 3.06/0.81  fof(f125,plain,(
% 3.06/0.81    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 3.06/0.81    inference(forward_demodulation,[],[f124,f51])).
% 3.06/0.81  fof(f51,plain,(
% 3.06/0.81    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.06/0.81    inference(cnf_transformation,[],[f17])).
% 3.06/0.81  fof(f17,axiom,(
% 3.06/0.81    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.06/0.81  fof(f124,plain,(
% 3.06/0.81    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 3.06/0.81    inference(forward_demodulation,[],[f119,f52])).
% 3.06/0.81  fof(f52,plain,(
% 3.06/0.81    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.06/0.81    inference(cnf_transformation,[],[f17])).
% 3.06/0.81  fof(f119,plain,(
% 3.06/0.81    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 3.06/0.81    inference(resolution,[],[f53,f49])).
% 3.06/0.81  fof(f49,plain,(
% 3.06/0.81    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f19])).
% 3.06/0.81  fof(f19,axiom,(
% 3.06/0.81    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.06/0.81  fof(f53,plain,(
% 3.06/0.81    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f28])).
% 3.06/0.81  fof(f28,plain,(
% 3.06/0.81    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.81    inference(ennf_transformation,[],[f16])).
% 3.06/0.81  fof(f16,axiom,(
% 3.06/0.81    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 3.06/0.81  fof(f1248,plain,(
% 3.06/0.81    ( ! [X2,X3] : (k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),k6_subset_1(X2,X3)) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2)) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1247,f125])).
% 3.06/0.81  fof(f1247,plain,(
% 3.06/0.81    ( ! [X2,X3] : (k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),k6_subset_1(X2,k10_relat_1(k6_relat_1(X3),X3)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1214,f399])).
% 3.06/0.81  fof(f399,plain,(
% 3.06/0.81    ( ! [X6,X8,X7] : (k6_subset_1(X6,k10_relat_1(k6_relat_1(X7),X8)) = k6_subset_1(X6,k10_relat_1(k7_relat_1(k6_relat_1(X7),X6),X8))) )),
% 3.06/0.81    inference(superposition,[],[f107,f179])).
% 3.06/0.81  fof(f179,plain,(
% 3.06/0.81    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k6_subset_1(X3,k6_subset_1(X3,k10_relat_1(k6_relat_1(X2),X4)))) )),
% 3.06/0.81    inference(resolution,[],[f109,f49])).
% 3.06/0.81  fof(f109,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f87,f84])).
% 3.06/0.81  fof(f87,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 3.06/0.81    inference(definition_unfolding,[],[f75,f79])).
% 3.06/0.81  fof(f75,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f37])).
% 3.06/0.81  fof(f37,plain,(
% 3.06/0.81    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.06/0.81    inference(ennf_transformation,[],[f21])).
% 3.06/0.81  fof(f21,axiom,(
% 3.06/0.81    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 3.06/0.81  fof(f107,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f85,f84])).
% 3.06/0.81  fof(f85,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.06/0.81    inference(definition_unfolding,[],[f67,f63,f63,f79])).
% 3.06/0.81  fof(f67,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f8])).
% 3.06/0.81  fof(f8,axiom,(
% 3.06/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.06/0.81  fof(f1214,plain,(
% 3.06/0.81    ( ! [X2,X3] : (k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),X2) = k10_relat_1(k6_relat_1(k6_subset_1(X2,X3)),k6_subset_1(X2,k10_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3)))) )),
% 3.06/0.81    inference(superposition,[],[f389,f391])).
% 3.06/0.81  fof(f391,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k6_subset_1(X1,k6_subset_1(X1,X0)) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.06/0.81    inference(superposition,[],[f179,f125])).
% 3.06/0.81  fof(f389,plain,(
% 3.06/0.81    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f381,f84])).
% 3.06/0.81  fof(f381,plain,(
% 3.06/0.81    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k6_relat_1(X4),k1_setfam_1(k2_enumset1(X5,X5,X5,X4)))) )),
% 3.06/0.81    inference(superposition,[],[f177,f141])).
% 3.06/0.81  fof(f141,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 3.06/0.81    inference(superposition,[],[f84,f83])).
% 3.06/0.81  fof(f83,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.06/0.81    inference(definition_unfolding,[],[f62,f78,f78])).
% 3.06/0.81  fof(f62,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f10])).
% 3.06/0.81  fof(f10,axiom,(
% 3.06/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.06/0.81  fof(f177,plain,(
% 3.06/0.81    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),k6_subset_1(X1,k6_subset_1(X1,X2)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f176,f52])).
% 3.06/0.81  fof(f176,plain,(
% 3.06/0.81    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),k6_subset_1(k2_relat_1(k6_relat_1(X1)),k6_subset_1(k2_relat_1(k6_relat_1(X1)),X2)))) )),
% 3.06/0.81    inference(resolution,[],[f108,f49])).
% 3.06/0.81  fof(f108,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k6_subset_1(k2_relat_1(X1),k6_subset_1(k2_relat_1(X1),X0)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f86,f84])).
% 3.06/0.81  fof(f86,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 3.06/0.81    inference(definition_unfolding,[],[f68,f79])).
% 3.06/0.81  fof(f68,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f32])).
% 3.06/0.81  fof(f32,plain,(
% 3.06/0.81    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.06/0.81    inference(ennf_transformation,[],[f15])).
% 3.06/0.81  fof(f15,axiom,(
% 3.06/0.81    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 3.06/0.81  fof(f1459,plain,(
% 3.06/0.81    k6_subset_1(k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),sK1),k6_subset_1(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(k6_subset_1(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) | ~spl5_23),
% 3.06/0.81    inference(superposition,[],[f416,f1440])).
% 3.06/0.81  fof(f1440,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) = k6_subset_1(sK1,k6_subset_1(sK1,k10_relat_1(sK0,sK2))) | ~spl5_23),
% 3.06/0.81    inference(avatar_component_clause,[],[f1439])).
% 3.06/0.81  fof(f416,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k6_subset_1(X1,X0)) = k6_subset_1(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.06/0.81    inference(superposition,[],[f190,f125])).
% 3.06/0.81  fof(f190,plain,(
% 3.06/0.81    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k6_subset_1(X3,X4)) = k6_subset_1(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 3.06/0.81    inference(global_subsumption,[],[f49,f185])).
% 3.06/0.81  fof(f185,plain,(
% 3.06/0.81    ( ! [X4,X2,X3] : (~v1_relat_1(k6_relat_1(X2)) | k10_relat_1(k6_relat_1(X2),k6_subset_1(X3,X4)) = k6_subset_1(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 3.06/0.81    inference(resolution,[],[f76,f50])).
% 3.06/0.81  fof(f50,plain,(
% 3.06/0.81    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f19])).
% 3.06/0.81  fof(f76,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 3.06/0.81    inference(cnf_transformation,[],[f39])).
% 3.06/0.81  fof(f39,plain,(
% 3.06/0.81    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.06/0.81    inference(flattening,[],[f38])).
% 3.06/0.81  fof(f38,plain,(
% 3.06/0.81    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.06/0.81    inference(ennf_transformation,[],[f20])).
% 3.06/0.81  fof(f20,axiom,(
% 3.06/0.81    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 3.06/0.81  fof(f1477,plain,(
% 3.06/0.81    spl5_26 | ~spl5_9 | ~spl5_23),
% 3.06/0.81    inference(avatar_split_clause,[],[f1453,f1439,f187,f1475])).
% 3.06/0.81  fof(f1475,plain,(
% 3.06/0.81    spl5_26 <=> r1_tarski(k10_relat_1(sK0,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK1))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 3.06/0.81  fof(f187,plain,(
% 3.06/0.81    spl5_9 <=> ! [X1,X0] : k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.06/0.81  fof(f1453,plain,(
% 3.06/0.81    r1_tarski(k10_relat_1(sK0,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK1)) | (~spl5_9 | ~spl5_23)),
% 3.06/0.81    inference(superposition,[],[f301,f1440])).
% 3.06/0.81  fof(f301,plain,(
% 3.06/0.81    ( ! [X12,X13] : (r1_tarski(k10_relat_1(sK0,k6_subset_1(X12,X13)),k10_relat_1(sK0,X12))) ) | ~spl5_9),
% 3.06/0.81    inference(superposition,[],[f82,f188])).
% 3.06/0.81  fof(f188,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl5_9),
% 3.06/0.81    inference(avatar_component_clause,[],[f187])).
% 3.06/0.81  fof(f82,plain,(
% 3.06/0.81    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.06/0.81    inference(definition_unfolding,[],[f61,f63])).
% 3.06/0.81  fof(f61,plain,(
% 3.06/0.81    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f5])).
% 3.06/0.81  fof(f5,axiom,(
% 3.06/0.81    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.06/0.81  fof(f1473,plain,(
% 3.06/0.81    spl5_25 | ~spl5_23),
% 3.06/0.81    inference(avatar_split_clause,[],[f1469,f1439,f1471])).
% 3.06/0.81  fof(f1471,plain,(
% 3.06/0.81    spl5_25 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.06/0.81  fof(f1469,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_23),
% 3.06/0.81    inference(forward_demodulation,[],[f1447,f125])).
% 3.06/0.81  fof(f1447,plain,(
% 3.06/0.81    k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~spl5_23),
% 3.06/0.81    inference(superposition,[],[f389,f1440])).
% 3.06/0.81  fof(f1468,plain,(
% 3.06/0.81    spl5_24 | ~spl5_23),
% 3.06/0.81    inference(avatar_split_clause,[],[f1464,f1439,f1466])).
% 3.06/0.81  fof(f1466,plain,(
% 3.06/0.81    spl5_24 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK0,sK2),sK1)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 3.06/0.81  fof(f1464,plain,(
% 3.06/0.81    k1_xboole_0 = k6_subset_1(k10_relat_1(sK0,sK2),sK1) | ~spl5_23),
% 3.06/0.81    inference(forward_demodulation,[],[f1444,f145])).
% 3.06/0.81  fof(f1444,plain,(
% 3.06/0.81    k6_subset_1(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) = k6_subset_1(k10_relat_1(sK0,sK2),sK1) | ~spl5_23),
% 3.06/0.81    inference(superposition,[],[f340,f1440])).
% 3.06/0.81  fof(f340,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X1,k6_subset_1(X1,X0)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f326,f84])).
% 3.06/0.81  fof(f326,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 3.06/0.81    inference(superposition,[],[f107,f141])).
% 3.06/0.81  fof(f1463,plain,(
% 3.06/0.81    spl5_3 | ~spl5_2 | ~spl5_23),
% 3.06/0.81    inference(avatar_split_clause,[],[f1443,f1439,f96,f100])).
% 3.06/0.81  fof(f100,plain,(
% 3.06/0.81    spl5_3 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.06/0.81  fof(f96,plain,(
% 3.06/0.81    spl5_2 <=> v1_relat_1(sK0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.06/0.81  fof(f1443,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl5_2 | ~spl5_23)),
% 3.06/0.81    inference(superposition,[],[f178,f1440])).
% 3.06/0.81  fof(f178,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(sK0,X1)))) ) | ~spl5_2),
% 3.06/0.81    inference(resolution,[],[f109,f97])).
% 3.06/0.81  fof(f97,plain,(
% 3.06/0.81    v1_relat_1(sK0) | ~spl5_2),
% 3.06/0.81    inference(avatar_component_clause,[],[f96])).
% 3.06/0.81  fof(f1462,plain,(
% 3.06/0.81    spl5_3 | ~spl5_2 | ~spl5_23),
% 3.06/0.81    inference(avatar_split_clause,[],[f1442,f1439,f96,f100])).
% 3.06/0.81  fof(f1442,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl5_2 | ~spl5_23)),
% 3.06/0.81    inference(superposition,[],[f1440,f178])).
% 3.06/0.81  fof(f1441,plain,(
% 3.06/0.81    spl5_23 | ~spl5_4),
% 3.06/0.81    inference(avatar_split_clause,[],[f1428,f104,f1439])).
% 3.06/0.81  fof(f104,plain,(
% 3.06/0.81    spl5_4 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.06/0.81  fof(f1428,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) = k6_subset_1(sK1,k6_subset_1(sK1,k10_relat_1(sK0,sK2))) | ~spl5_4),
% 3.06/0.81    inference(resolution,[],[f1411,f105])).
% 3.06/0.81  fof(f105,plain,(
% 3.06/0.81    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl5_4),
% 3.06/0.81    inference(avatar_component_clause,[],[f104])).
% 3.06/0.81  fof(f1411,plain,(
% 3.06/0.81    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k6_subset_1(X1,k6_subset_1(X1,X2)) = X2) )),
% 3.06/0.81    inference(backward_demodulation,[],[f174,f1410])).
% 3.06/0.81  fof(f1410,plain,(
% 3.06/0.81    ( ! [X6,X5] : (k6_subset_1(X5,k6_subset_1(X5,X6)) = k9_relat_1(k6_relat_1(X5),k10_relat_1(k6_relat_1(X5),X6))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1409,f1321])).
% 3.06/0.81  fof(f1321,plain,(
% 3.06/0.81    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k7_relat_1(k6_relat_1(X4),X4),X5)) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1320,f389])).
% 3.06/0.81  fof(f1320,plain,(
% 3.06/0.81    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) = k10_relat_1(k7_relat_1(k6_relat_1(X4),X4),X5)) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1319,f179])).
% 3.06/0.81  fof(f1319,plain,(
% 3.06/0.81    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) = k6_subset_1(X4,k6_subset_1(X4,k10_relat_1(k6_relat_1(X4),X5)))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1286,f414])).
% 3.06/0.81  fof(f414,plain,(
% 3.06/0.81    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1)) = k6_subset_1(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 3.06/0.81    inference(superposition,[],[f190,f125])).
% 3.06/0.81  fof(f1286,plain,(
% 3.06/0.81    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),k6_subset_1(X5,k6_subset_1(X5,X4))) = k6_subset_1(X4,k10_relat_1(k6_relat_1(X4),k6_subset_1(X4,X5)))) )),
% 3.06/0.81    inference(superposition,[],[f414,f324])).
% 3.06/0.81  fof(f324,plain,(
% 3.06/0.81    ( ! [X4,X3] : (k6_subset_1(X3,k6_subset_1(X3,X4)) = k6_subset_1(X4,k6_subset_1(X4,X3))) )),
% 3.06/0.81    inference(superposition,[],[f141,f84])).
% 3.06/0.81  fof(f1409,plain,(
% 3.06/0.81    ( ! [X6,X5] : (k6_subset_1(X5,k6_subset_1(X5,X6)) = k9_relat_1(k6_relat_1(X5),k10_relat_1(k7_relat_1(k6_relat_1(X5),X5),X6))) )),
% 3.06/0.81    inference(forward_demodulation,[],[f1401,f179])).
% 3.06/0.81  fof(f1401,plain,(
% 3.06/0.81    ( ! [X6,X5] : (k6_subset_1(X5,k6_subset_1(X5,X6)) = k9_relat_1(k6_relat_1(X5),k6_subset_1(X5,k6_subset_1(X5,k10_relat_1(k6_relat_1(X5),X6))))) )),
% 3.06/0.81    inference(superposition,[],[f427,f414])).
% 3.06/0.81  fof(f427,plain,(
% 3.06/0.81    ( ! [X2,X3] : (k6_subset_1(X2,X3) = k9_relat_1(k6_relat_1(X2),k6_subset_1(X2,k10_relat_1(k6_relat_1(X2),X3)))) )),
% 3.06/0.81    inference(backward_demodulation,[],[f355,f414])).
% 3.06/0.81  fof(f355,plain,(
% 3.06/0.81    ( ! [X2,X3] : (k6_subset_1(X2,X3) = k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),k6_subset_1(X2,X3)))) )),
% 3.06/0.81    inference(resolution,[],[f174,f82])).
% 3.06/0.81  fof(f174,plain,(
% 3.06/0.81    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 3.06/0.81    inference(global_subsumption,[],[f49,f173])).
% 3.06/0.81  fof(f173,plain,(
% 3.06/0.81    ( ! [X2,X1] : (~r1_tarski(X2,X1) | ~v1_relat_1(k6_relat_1(X1)) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 3.06/0.81    inference(forward_demodulation,[],[f168,f52])).
% 3.06/0.81  fof(f168,plain,(
% 3.06/0.81    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~r1_tarski(X2,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 3.06/0.81    inference(resolution,[],[f69,f50])).
% 3.06/0.81  fof(f69,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 3.06/0.81    inference(cnf_transformation,[],[f34])).
% 3.06/0.81  fof(f34,plain,(
% 3.06/0.81    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.06/0.81    inference(flattening,[],[f33])).
% 3.06/0.81  fof(f33,plain,(
% 3.06/0.81    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.06/0.81    inference(ennf_transformation,[],[f22])).
% 3.06/0.81  fof(f22,axiom,(
% 3.06/0.81    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 3.06/0.81  fof(f1282,plain,(
% 3.06/0.81    ~spl5_22 | ~spl5_6 | ~spl5_14),
% 3.06/0.81    inference(avatar_split_clause,[],[f1278,f307,f151,f1280])).
% 3.06/0.81  fof(f1280,plain,(
% 3.06/0.81    spl5_22 <=> r2_hidden(k1_relat_1(sK0),k1_xboole_0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.06/0.81  fof(f151,plain,(
% 3.06/0.81    spl5_6 <=> ! [X1,X0] : (r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k10_relat_1(sK0,X1)))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.06/0.81  fof(f307,plain,(
% 3.06/0.81    spl5_14 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.06/0.81  fof(f1278,plain,(
% 3.06/0.81    ~r2_hidden(k1_relat_1(sK0),k1_xboole_0) | (~spl5_6 | ~spl5_14)),
% 3.06/0.81    inference(resolution,[],[f1079,f110])).
% 3.06/0.81  fof(f110,plain,(
% 3.06/0.81    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.06/0.81    inference(superposition,[],[f82,f81])).
% 3.06/0.81  fof(f1079,plain,(
% 3.06/0.81    ( ! [X2] : (~r1_tarski(k1_relat_1(sK0),X2) | ~r2_hidden(X2,k1_xboole_0)) ) | (~spl5_6 | ~spl5_14)),
% 3.06/0.81    inference(resolution,[],[f368,f73])).
% 3.06/0.81  fof(f73,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f36])).
% 3.06/0.81  fof(f36,plain,(
% 3.06/0.81    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.06/0.81    inference(ennf_transformation,[],[f23])).
% 3.06/0.81  fof(f23,axiom,(
% 3.06/0.81    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.06/0.81  fof(f368,plain,(
% 3.06/0.81    ( ! [X4] : (r2_hidden(X4,k1_relat_1(sK0)) | ~r2_hidden(X4,k1_xboole_0)) ) | (~spl5_6 | ~spl5_14)),
% 3.06/0.81    inference(superposition,[],[f152,f308])).
% 3.06/0.81  fof(f308,plain,(
% 3.06/0.81    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl5_14),
% 3.06/0.81    inference(avatar_component_clause,[],[f307])).
% 3.06/0.81  fof(f152,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,X1)) | r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl5_6),
% 3.06/0.81    inference(avatar_component_clause,[],[f151])).
% 3.06/0.81  fof(f1211,plain,(
% 3.06/0.81    ~spl5_2 | ~spl5_1 | spl5_21 | ~spl5_10),
% 3.06/0.81    inference(avatar_split_clause,[],[f1207,f194,f1209,f92,f96])).
% 3.06/0.81  fof(f92,plain,(
% 3.06/0.81    spl5_1 <=> v1_funct_1(sK0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.06/0.81  fof(f1209,plain,(
% 3.06/0.81    spl5_21 <=> ! [X3] : (k1_relat_1(sK0) = k10_relat_1(sK0,X3) | ~r2_hidden(k1_funct_1(sK0,sK3(sK0,X3,k1_relat_1(sK0))),X3) | ~r2_hidden(sK3(sK0,X3,k1_relat_1(sK0)),k1_relat_1(sK0)))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 3.06/0.81  fof(f194,plain,(
% 3.06/0.81    spl5_10 <=> ! [X1,X0] : (r2_hidden(sK3(sK0,X0,X1),k1_relat_1(sK0)) | k10_relat_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.06/0.81  fof(f1207,plain,(
% 3.06/0.81    ( ! [X3] : (k1_relat_1(sK0) = k10_relat_1(sK0,X3) | ~v1_funct_1(sK0) | ~r2_hidden(sK3(sK0,X3,k1_relat_1(sK0)),k1_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK0,sK3(sK0,X3,k1_relat_1(sK0))),X3) | ~v1_relat_1(sK0)) ) | ~spl5_10),
% 3.06/0.81    inference(duplicate_literal_removal,[],[f1206])).
% 3.06/0.81  fof(f1206,plain,(
% 3.06/0.81    ( ! [X3] : (k1_relat_1(sK0) = k10_relat_1(sK0,X3) | ~v1_funct_1(sK0) | ~r2_hidden(sK3(sK0,X3,k1_relat_1(sK0)),k1_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK0,sK3(sK0,X3,k1_relat_1(sK0))),X3) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k10_relat_1(sK0,X3)) ) | ~spl5_10),
% 3.06/0.81    inference(resolution,[],[f446,f55])).
% 3.06/0.81  fof(f55,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) | ~v1_relat_1(X0) | k10_relat_1(X0,X1) = X2) )),
% 3.06/0.81    inference(cnf_transformation,[],[f31])).
% 3.06/0.81  fof(f31,plain,(
% 3.06/0.81    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.81    inference(flattening,[],[f30])).
% 3.06/0.81  fof(f30,plain,(
% 3.06/0.81    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/0.81    inference(ennf_transformation,[],[f18])).
% 3.06/0.81  fof(f18,axiom,(
% 3.06/0.81    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 3.06/0.81  fof(f446,plain,(
% 3.06/0.81    ( ! [X0] : (r2_hidden(sK3(sK0,X0,k1_relat_1(sK0)),k1_relat_1(sK0)) | k1_relat_1(sK0) = k10_relat_1(sK0,X0)) ) | ~spl5_10),
% 3.06/0.81    inference(factoring,[],[f195])).
% 3.06/0.81  fof(f195,plain,(
% 3.06/0.81    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),k1_relat_1(sK0)) | r2_hidden(sK3(sK0,X0,X1),X1) | k10_relat_1(sK0,X0) = X1) ) | ~spl5_10),
% 3.06/0.81    inference(avatar_component_clause,[],[f194])).
% 3.06/0.81  fof(f1051,plain,(
% 3.06/0.81    spl5_20 | ~spl5_2 | ~spl5_5 | ~spl5_9),
% 3.06/0.81    inference(avatar_split_clause,[],[f1047,f187,f121,f96,f1049])).
% 3.06/0.81  fof(f1049,plain,(
% 3.06/0.81    spl5_20 <=> k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 3.06/0.81  fof(f121,plain,(
% 3.06/0.81    spl5_5 <=> k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.06/0.81  fof(f1047,plain,(
% 3.06/0.81    k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0)) | (~spl5_2 | ~spl5_5 | ~spl5_9)),
% 3.06/0.81    inference(forward_demodulation,[],[f1046,f122])).
% 3.06/0.81  fof(f122,plain,(
% 3.06/0.81    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0) | ~spl5_5),
% 3.06/0.81    inference(avatar_component_clause,[],[f121])).
% 3.06/0.81  fof(f1046,plain,(
% 3.06/0.81    k10_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0)) | (~spl5_2 | ~spl5_5 | ~spl5_9)),
% 3.06/0.81    inference(forward_demodulation,[],[f1045,f284])).
% 3.06/0.81  fof(f284,plain,(
% 3.06/0.81    ( ! [X17] : (k10_relat_1(sK0,k10_relat_1(sK0,X17)) = k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),X17))) ) | ~spl5_2),
% 3.06/0.81    inference(superposition,[],[f175,f178])).
% 3.06/0.81  fof(f175,plain,(
% 3.06/0.81    ( ! [X0] : (k10_relat_1(sK0,X0) = k10_relat_1(sK0,k6_subset_1(k2_relat_1(sK0),k6_subset_1(k2_relat_1(sK0),X0)))) ) | ~spl5_2),
% 3.06/0.81    inference(resolution,[],[f108,f97])).
% 3.06/0.81  fof(f1045,plain,(
% 3.06/0.81    k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k1_relat_1(sK0)) | (~spl5_2 | ~spl5_5 | ~spl5_9)),
% 3.06/0.81    inference(forward_demodulation,[],[f1044,f178])).
% 3.06/0.81  fof(f1044,plain,(
% 3.06/0.81    k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) = k6_subset_1(k1_relat_1(sK0),k6_subset_1(k1_relat_1(sK0),k10_relat_1(sK0,k1_relat_1(sK0)))) | (~spl5_2 | ~spl5_5 | ~spl5_9)),
% 3.06/0.81    inference(forward_demodulation,[],[f1013,f290])).
% 3.06/0.81  fof(f290,plain,(
% 3.06/0.81    ( ! [X0] : (k10_relat_1(sK0,k6_subset_1(k2_relat_1(sK0),X0)) = k6_subset_1(k1_relat_1(sK0),k10_relat_1(sK0,X0))) ) | (~spl5_5 | ~spl5_9)),
% 3.06/0.81    inference(superposition,[],[f188,f122])).
% 3.06/0.81  fof(f1013,plain,(
% 3.06/0.81    k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) = k6_subset_1(k1_relat_1(sK0),k10_relat_1(sK0,k6_subset_1(k2_relat_1(sK0),k1_relat_1(sK0)))) | (~spl5_2 | ~spl5_5 | ~spl5_9)),
% 3.06/0.81    inference(superposition,[],[f290,f271])).
% 3.06/0.81  fof(f271,plain,(
% 3.06/0.81    ( ! [X0] : (k10_relat_1(k7_relat_1(sK0,X0),k2_relat_1(sK0)) = k6_subset_1(X0,k6_subset_1(X0,k1_relat_1(sK0)))) ) | (~spl5_2 | ~spl5_5)),
% 3.06/0.81    inference(superposition,[],[f178,f122])).
% 3.06/0.81  fof(f977,plain,(
% 3.06/0.81    spl5_19 | ~spl5_2 | ~spl5_5),
% 3.06/0.81    inference(avatar_split_clause,[],[f962,f121,f96,f975])).
% 3.06/0.81  fof(f975,plain,(
% 3.06/0.81    spl5_19 <=> k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0)))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.06/0.81  fof(f962,plain,(
% 3.06/0.81    k10_relat_1(sK0,k1_relat_1(sK0)) = k10_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,k2_relat_1(sK0)),k2_relat_1(sK0))) | (~spl5_2 | ~spl5_5)),
% 3.06/0.81    inference(superposition,[],[f175,f271])).
% 3.06/0.81  fof(f655,plain,(
% 3.06/0.81    spl5_18 | ~spl5_2 | ~spl5_5),
% 3.06/0.81    inference(avatar_split_clause,[],[f647,f121,f96,f653])).
% 3.06/0.81  fof(f653,plain,(
% 3.06/0.81    spl5_18 <=> k1_relat_1(sK0) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k2_relat_1(sK0))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.06/0.81  fof(f647,plain,(
% 3.06/0.81    k1_relat_1(sK0) = k10_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),k2_relat_1(sK0)) | (~spl5_2 | ~spl5_5)),
% 3.06/0.81    inference(superposition,[],[f287,f122])).
% 3.06/0.81  fof(f287,plain,(
% 3.06/0.81    ( ! [X0] : (k10_relat_1(sK0,X0) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) ) | ~spl5_2),
% 3.06/0.81    inference(forward_demodulation,[],[f273,f81])).
% 3.06/0.81  fof(f273,plain,(
% 3.06/0.81    ( ! [X0] : (k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k6_subset_1(k10_relat_1(sK0,X0),k1_xboole_0)) ) | ~spl5_2),
% 3.06/0.81    inference(superposition,[],[f178,f145])).
% 3.06/0.81  fof(f468,plain,(
% 3.06/0.81    ~spl5_2 | ~spl5_1 | spl5_17 | ~spl5_11),
% 3.06/0.81    inference(avatar_split_clause,[],[f451,f202,f466,f92,f96])).
% 3.06/0.81  fof(f466,plain,(
% 3.06/0.81    spl5_17 <=> ! [X5,X6] : (r2_hidden(sK3(sK0,X5,X6),X6) | r2_hidden(sK3(sK0,X5,X6),k10_relat_1(sK0,X5)) | ~r2_hidden(sK3(sK0,X5,X6),k1_relat_1(sK0)) | k10_relat_1(sK0,X5) = X6)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 3.06/0.81  fof(f202,plain,(
% 3.06/0.81    spl5_11 <=> ! [X1,X0] : (r2_hidden(k1_funct_1(sK0,sK3(sK0,X0,X1)),X0) | k10_relat_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.06/0.81  fof(f451,plain,(
% 3.06/0.81    ( ! [X6,X5] : (r2_hidden(sK3(sK0,X5,X6),X6) | k10_relat_1(sK0,X5) = X6 | ~v1_funct_1(sK0) | ~r2_hidden(sK3(sK0,X5,X6),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r2_hidden(sK3(sK0,X5,X6),k10_relat_1(sK0,X5))) ) | ~spl5_11),
% 3.06/0.81    inference(resolution,[],[f203,f88])).
% 3.06/0.81  fof(f88,plain,(
% 3.06/0.81    ( ! [X0,X3,X1] : (~r2_hidden(k1_funct_1(X0,X3),X1) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 3.06/0.81    inference(equality_resolution,[],[f60])).
% 3.06/0.81  fof(f60,plain,(
% 3.06/0.81    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,X3),X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 3.06/0.81    inference(cnf_transformation,[],[f31])).
% 3.06/0.81  fof(f203,plain,(
% 3.06/0.81    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK0,sK3(sK0,X0,X1)),X0) | r2_hidden(sK3(sK0,X0,X1),X1) | k10_relat_1(sK0,X0) = X1) ) | ~spl5_11),
% 3.06/0.81    inference(avatar_component_clause,[],[f202])).
% 3.06/0.81  fof(f363,plain,(
% 3.06/0.81    spl5_16 | ~spl5_4),
% 3.06/0.81    inference(avatar_split_clause,[],[f358,f104,f361])).
% 3.06/0.81  fof(f361,plain,(
% 3.06/0.81    spl5_16 <=> k10_relat_1(sK0,sK2) = k9_relat_1(k6_relat_1(sK1),k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 3.06/0.81  fof(f358,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) = k9_relat_1(k6_relat_1(sK1),k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) | ~spl5_4),
% 3.06/0.81    inference(resolution,[],[f174,f105])).
% 3.06/0.81  fof(f317,plain,(
% 3.06/0.81    spl5_15 | ~spl5_13 | ~spl5_14),
% 3.06/0.81    inference(avatar_split_clause,[],[f313,f307,f257,f315])).
% 3.06/0.81  fof(f315,plain,(
% 3.06/0.81    spl5_15 <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.06/0.81  fof(f257,plain,(
% 3.06/0.81    spl5_13 <=> k1_xboole_0 = k9_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.06/0.81  fof(f313,plain,(
% 3.06/0.81    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) | (~spl5_13 | ~spl5_14)),
% 3.06/0.81    inference(backward_demodulation,[],[f258,f308])).
% 3.06/0.81  fof(f258,plain,(
% 3.06/0.81    k1_xboole_0 = k9_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | ~spl5_13),
% 3.06/0.81    inference(avatar_component_clause,[],[f257])).
% 3.06/0.81  fof(f311,plain,(
% 3.06/0.81    spl5_14 | ~spl5_9),
% 3.06/0.81    inference(avatar_split_clause,[],[f310,f187,f307])).
% 3.06/0.81  fof(f310,plain,(
% 3.06/0.81    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl5_9),
% 3.06/0.81    inference(forward_demodulation,[],[f297,f145])).
% 3.06/0.81  fof(f297,plain,(
% 3.06/0.81    ( ! [X3] : (k1_xboole_0 = k10_relat_1(sK0,k6_subset_1(X3,X3))) ) | ~spl5_9),
% 3.06/0.81    inference(superposition,[],[f145,f188])).
% 3.06/0.81  fof(f309,plain,(
% 3.06/0.81    spl5_14 | ~spl5_9),
% 3.06/0.81    inference(avatar_split_clause,[],[f305,f187,f307])).
% 3.06/0.81  fof(f305,plain,(
% 3.06/0.81    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl5_9),
% 3.06/0.81    inference(forward_demodulation,[],[f294,f145])).
% 3.06/0.81  fof(f294,plain,(
% 3.06/0.81    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK0,k6_subset_1(X2,X2))) ) | ~spl5_9),
% 3.06/0.81    inference(superposition,[],[f188,f145])).
% 3.06/0.81  fof(f259,plain,(
% 3.06/0.81    spl5_13 | ~spl5_8),
% 3.06/0.81    inference(avatar_split_clause,[],[f248,f170,f257])).
% 3.06/0.81  fof(f170,plain,(
% 3.06/0.81    spl5_8 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK0)) | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0)),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.06/0.81  fof(f248,plain,(
% 3.06/0.81    k1_xboole_0 = k9_relat_1(sK0,k10_relat_1(sK0,k1_xboole_0)) | ~spl5_8),
% 3.06/0.81    inference(resolution,[],[f171,f46])).
% 3.06/0.81  fof(f46,plain,(
% 3.06/0.81    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.06/0.81    inference(cnf_transformation,[],[f4])).
% 3.06/0.81  fof(f4,axiom,(
% 3.06/0.81    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.06/0.81  fof(f171,plain,(
% 3.06/0.81    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK0)) | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0) ) | ~spl5_8),
% 3.06/0.81    inference(avatar_component_clause,[],[f170])).
% 3.06/0.81  fof(f255,plain,(
% 3.06/0.81    spl5_12 | ~spl5_5 | ~spl5_8),
% 3.06/0.81    inference(avatar_split_clause,[],[f251,f170,f121,f253])).
% 3.06/0.81  fof(f253,plain,(
% 3.06/0.81    spl5_12 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.06/0.81  fof(f251,plain,(
% 3.06/0.81    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl5_5 | ~spl5_8)),
% 3.06/0.81    inference(forward_demodulation,[],[f247,f122])).
% 3.06/0.81  fof(f247,plain,(
% 3.06/0.81    k2_relat_1(sK0) = k9_relat_1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))) | ~spl5_8),
% 3.06/0.81    inference(resolution,[],[f171,f110])).
% 3.06/0.81  fof(f204,plain,(
% 3.06/0.81    spl5_11 | ~spl5_2 | ~spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f199,f92,f96,f202])).
% 3.06/0.81  fof(f199,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(sK0) | r2_hidden(k1_funct_1(sK0,sK3(sK0,X0,X1)),X0) | r2_hidden(sK3(sK0,X0,X1),X1) | k10_relat_1(sK0,X0) = X1) ) | ~spl5_1),
% 3.06/0.81    inference(resolution,[],[f57,f93])).
% 3.06/0.81  fof(f93,plain,(
% 3.06/0.81    v1_funct_1(sK0) | ~spl5_1),
% 3.06/0.81    inference(avatar_component_clause,[],[f92])).
% 3.06/0.81  fof(f57,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 3.06/0.81    inference(cnf_transformation,[],[f31])).
% 3.06/0.81  fof(f196,plain,(
% 3.06/0.81    spl5_10 | ~spl5_2 | ~spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f191,f92,f96,f194])).
% 3.06/0.81  fof(f191,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(sK0) | r2_hidden(sK3(sK0,X0,X1),k1_relat_1(sK0)) | r2_hidden(sK3(sK0,X0,X1),X1) | k10_relat_1(sK0,X0) = X1) ) | ~spl5_1),
% 3.06/0.81    inference(resolution,[],[f56,f93])).
% 3.06/0.81  fof(f56,plain,(
% 3.06/0.81    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK3(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 3.06/0.81    inference(cnf_transformation,[],[f31])).
% 3.06/0.81  fof(f189,plain,(
% 3.06/0.81    spl5_9 | ~spl5_2 | ~spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f184,f92,f96,f187])).
% 3.06/0.81  fof(f184,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(sK0) | k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl5_1),
% 3.06/0.81    inference(resolution,[],[f76,f93])).
% 3.06/0.81  fof(f172,plain,(
% 3.06/0.81    spl5_8 | ~spl5_2 | ~spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f167,f92,f96,f170])).
% 3.06/0.81  fof(f167,plain,(
% 3.06/0.81    ( ! [X0] : (~v1_relat_1(sK0) | ~r1_tarski(X0,k2_relat_1(sK0)) | k9_relat_1(sK0,k10_relat_1(sK0,X0)) = X0) ) | ~spl5_1),
% 3.06/0.81    inference(resolution,[],[f69,f93])).
% 3.06/0.81  fof(f165,plain,(
% 3.06/0.81    spl5_7 | ~spl5_2 | ~spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f160,f92,f96,f163])).
% 3.06/0.81  fof(f163,plain,(
% 3.06/0.81    spl5_7 <=> ! [X1,X0] : (r2_hidden(k1_funct_1(sK0,X0),X1) | ~r2_hidden(X0,k10_relat_1(sK0,X1)))),
% 3.06/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.06/0.81  fof(f160,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(sK0) | r2_hidden(k1_funct_1(sK0,X0),X1) | ~r2_hidden(X0,k10_relat_1(sK0,X1))) ) | ~spl5_1),
% 3.06/0.81    inference(resolution,[],[f89,f93])).
% 3.06/0.81  fof(f89,plain,(
% 3.06/0.81    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 3.06/0.81    inference(equality_resolution,[],[f59])).
% 3.06/0.81  fof(f59,plain,(
% 3.06/0.81    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 3.06/0.81    inference(cnf_transformation,[],[f31])).
% 3.06/0.81  fof(f154,plain,(
% 3.06/0.81    spl5_6 | ~spl5_2 | ~spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f148,f92,f96,f151])).
% 3.06/0.81  fof(f148,plain,(
% 3.06/0.81    ( ! [X0,X1] : (~v1_relat_1(sK0) | r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k10_relat_1(sK0,X1))) ) | ~spl5_1),
% 3.06/0.81    inference(resolution,[],[f90,f93])).
% 3.06/0.81  fof(f90,plain,(
% 3.06/0.81    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 3.06/0.81    inference(equality_resolution,[],[f58])).
% 3.06/0.81  fof(f58,plain,(
% 3.06/0.81    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 3.06/0.81    inference(cnf_transformation,[],[f31])).
% 3.06/0.81  fof(f123,plain,(
% 3.06/0.81    spl5_5 | ~spl5_2),
% 3.06/0.81    inference(avatar_split_clause,[],[f118,f96,f121])).
% 3.06/0.81  fof(f118,plain,(
% 3.06/0.81    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(sK0) | ~spl5_2),
% 3.06/0.81    inference(resolution,[],[f53,f97])).
% 3.06/0.81  fof(f106,plain,(
% 3.06/0.81    spl5_4),
% 3.06/0.81    inference(avatar_split_clause,[],[f42,f104])).
% 3.06/0.81  fof(f42,plain,(
% 3.06/0.81    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 3.06/0.81    inference(cnf_transformation,[],[f27])).
% 3.06/0.81  fof(f27,plain,(
% 3.06/0.81    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.06/0.81    inference(flattening,[],[f26])).
% 3.06/0.81  fof(f26,plain,(
% 3.06/0.81    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.06/0.81    inference(ennf_transformation,[],[f25])).
% 3.06/0.81  fof(f25,negated_conjecture,(
% 3.06/0.81    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.06/0.81    inference(negated_conjecture,[],[f24])).
% 3.06/0.81  fof(f24,conjecture,(
% 3.06/0.81    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.06/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 3.06/0.81  fof(f102,plain,(
% 3.06/0.81    ~spl5_3),
% 3.06/0.81    inference(avatar_split_clause,[],[f43,f100])).
% 3.06/0.81  fof(f43,plain,(
% 3.06/0.81    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 3.06/0.81    inference(cnf_transformation,[],[f27])).
% 3.06/0.81  fof(f98,plain,(
% 3.06/0.81    spl5_2),
% 3.06/0.81    inference(avatar_split_clause,[],[f44,f96])).
% 3.06/0.81  fof(f44,plain,(
% 3.06/0.81    v1_relat_1(sK0)),
% 3.06/0.81    inference(cnf_transformation,[],[f27])).
% 3.06/0.81  fof(f94,plain,(
% 3.06/0.81    spl5_1),
% 3.06/0.81    inference(avatar_split_clause,[],[f45,f92])).
% 3.06/0.81  fof(f45,plain,(
% 3.06/0.81    v1_funct_1(sK0)),
% 3.06/0.81    inference(cnf_transformation,[],[f27])).
% 3.06/0.81  % SZS output end Proof for theBenchmark
% 3.06/0.81  % (15047)------------------------------
% 3.06/0.81  % (15047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.81  % (15047)Termination reason: Refutation
% 3.06/0.81  
% 3.06/0.81  % (15047)Memory used [KB]: 7675
% 3.06/0.81  % (15047)Time elapsed: 0.399 s
% 3.06/0.81  % (15047)------------------------------
% 3.06/0.81  % (15047)------------------------------
% 3.06/0.83  % (15024)Time limit reached!
% 3.06/0.83  % (15024)------------------------------
% 3.06/0.83  % (15024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.83  % (15024)Termination reason: Time limit
% 3.06/0.83  % (15024)Termination phase: Saturation
% 3.06/0.83  
% 3.06/0.83  % (15024)Memory used [KB]: 8827
% 3.06/0.83  % (15024)Time elapsed: 0.400 s
% 3.06/0.83  % (15024)------------------------------
% 3.06/0.83  % (15024)------------------------------
% 3.63/0.84  % (15018)Success in time 0.473 s
%------------------------------------------------------------------------------
