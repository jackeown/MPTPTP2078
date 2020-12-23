%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:58 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 236 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  264 ( 457 expanded)
%              Number of equality atoms :   59 ( 127 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1808,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f253,f492,f965,f1000,f1038,f1045,f1083,f1806,f1807])).

fof(f1807,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1806,plain,
    ( spl4_124
    | ~ spl4_3
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1801,f993,f85,f1803])).

fof(f1803,plain,
    ( spl4_124
  <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f85,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f993,plain,
    ( spl4_64
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1801,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_3
    | ~ spl4_64 ),
    inference(superposition,[],[f123,f995])).

fof(f995,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f993])).

fof(f123,plain,
    ( ! [X2,X1] : k2_wellord1(k2_wellord1(sK2,X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(sK2,X1),X2))
    | ~ spl4_3 ),
    inference(resolution,[],[f45,f89])).

fof(f89,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK2,X0))
    | ~ spl4_3 ),
    inference(resolution,[],[f44,f87])).

fof(f87,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f1083,plain,
    ( spl4_74
    | ~ spl4_65
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f1072,f1035,f997,f1080])).

fof(f1080,plain,
    ( spl4_74
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f997,plain,
    ( spl4_65
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1035,plain,
    ( spl4_70
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1072,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_70 ),
    inference(resolution,[],[f1037,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f1037,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1045,plain,
    ( ~ spl4_3
    | spl4_65 ),
    inference(avatar_contradiction_clause,[],[f1044])).

fof(f1044,plain,
    ( $false
    | ~ spl4_3
    | spl4_65 ),
    inference(resolution,[],[f999,f89])).

fof(f999,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f997])).

fof(f1038,plain,
    ( spl4_70
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1019,f489,f85,f1035])).

fof(f489,plain,
    ( spl4_37
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1019,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(resolution,[],[f883,f491])).

fof(f491,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f489])).

fof(f883,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X8)),X9)
        | r1_tarski(k2_relat_1(k2_wellord1(sK2,X8)),X9) )
    | ~ spl4_3 ),
    inference(superposition,[],[f264,f205])).

fof(f205,plain,
    ( ! [X0] : k3_relat_1(k2_wellord1(sK2,X0)) = k3_tarski(k5_enumset1(k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k2_relat_1(k2_wellord1(sK2,X0))))
    | ~ spl4_3 ),
    inference(resolution,[],[f69,f89])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f264,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X7)),X8)
      | r1_tarski(X7,X8) ) ),
    inference(resolution,[],[f197,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f197,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(resolution,[],[f70,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1000,plain,
    ( spl4_64
    | ~ spl4_65
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f985,f962,f997,f993])).

fof(f962,plain,
    ( spl4_61
  <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f985,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_61 ),
    inference(resolution,[],[f964,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f964,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f962])).

fof(f965,plain,
    ( spl4_61
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f946,f489,f85,f962])).

fof(f946,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(resolution,[],[f878,f491])).

fof(f878,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)
        | r1_tarski(k1_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f71,f205])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f492,plain,
    ( spl4_37
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f469,f85,f80,f489])).

fof(f80,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f469,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f420,f82])).

fof(f82,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f420,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X5) )
    | ~ spl4_3 ),
    inference(resolution,[],[f417,f60])).

fof(f417,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f281,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f281,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f146,f87])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f253,plain,
    ( ~ spl4_19
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f240,f85,f75,f249])).

fof(f249,plain,
    ( spl4_19
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f75,plain,
    ( spl4_1
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f240,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f77,f172])).

fof(f172,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f87])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f77,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f83,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f39,f80])).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (1893)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (1918)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (1910)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (1905)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (1909)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (1899)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (1894)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (1895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1907)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (1921)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (1892)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1914)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (1916)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (1908)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (1920)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (1908)Refutation not found, incomplete strategy% (1908)------------------------------
% 0.21/0.55  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1908)Memory used [KB]: 10618
% 0.21/0.55  % (1908)Time elapsed: 0.126 s
% 0.21/0.55  % (1908)------------------------------
% 0.21/0.55  % (1908)------------------------------
% 0.21/0.55  % (1919)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (1906)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (1898)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (1911)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (1903)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (1900)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (1896)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (1897)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (1913)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (1902)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (1915)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (1891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.55/0.59  % (1917)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.55/0.60  % (1901)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.60  % (1904)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.86/0.65  % (1907)Refutation found. Thanks to Tanya!
% 1.86/0.65  % SZS status Theorem for theBenchmark
% 1.86/0.65  % SZS output start Proof for theBenchmark
% 1.86/0.65  fof(f1808,plain,(
% 1.86/0.65    $false),
% 1.86/0.65    inference(avatar_sat_refutation,[],[f78,f83,f88,f253,f492,f965,f1000,f1038,f1045,f1083,f1806,f1807])).
% 1.86/0.65  fof(f1807,plain,(
% 1.86/0.65    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.86/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.86/0.65  fof(f1806,plain,(
% 1.86/0.65    spl4_124 | ~spl4_3 | ~spl4_64),
% 1.86/0.65    inference(avatar_split_clause,[],[f1801,f993,f85,f1803])).
% 1.86/0.65  fof(f1803,plain,(
% 1.86/0.65    spl4_124 <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).
% 1.86/0.65  fof(f85,plain,(
% 1.86/0.65    spl4_3 <=> v1_relat_1(sK2)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.86/0.65  fof(f993,plain,(
% 1.86/0.65    spl4_64 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 1.86/0.65  fof(f1801,plain,(
% 1.86/0.65    k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | (~spl4_3 | ~spl4_64)),
% 1.86/0.65    inference(superposition,[],[f123,f995])).
% 1.86/0.65  fof(f995,plain,(
% 1.86/0.65    k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl4_64),
% 1.86/0.65    inference(avatar_component_clause,[],[f993])).
% 1.86/0.65  fof(f123,plain,(
% 1.86/0.65    ( ! [X2,X1] : (k2_wellord1(k2_wellord1(sK2,X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(sK2,X1),X2))) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f45,f89])).
% 1.86/0.65  fof(f89,plain,(
% 1.86/0.65    ( ! [X0] : (v1_relat_1(k2_wellord1(sK2,X0))) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f44,f87])).
% 1.86/0.65  fof(f87,plain,(
% 1.86/0.65    v1_relat_1(sK2) | ~spl4_3),
% 1.86/0.65    inference(avatar_component_clause,[],[f85])).
% 1.86/0.65  fof(f44,plain,(
% 1.86/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f24])).
% 1.86/0.65  fof(f24,plain,(
% 1.86/0.65    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.86/0.65    inference(ennf_transformation,[],[f15])).
% 1.86/0.65  fof(f15,axiom,(
% 1.86/0.65    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.86/0.65  fof(f45,plain,(
% 1.86/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f25])).
% 1.86/0.65  fof(f25,plain,(
% 1.86/0.65    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.86/0.65    inference(ennf_transformation,[],[f16])).
% 1.86/0.65  fof(f16,axiom,(
% 1.86/0.65    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 1.86/0.65  fof(f1083,plain,(
% 1.86/0.65    spl4_74 | ~spl4_65 | ~spl4_70),
% 1.86/0.65    inference(avatar_split_clause,[],[f1072,f1035,f997,f1080])).
% 1.86/0.65  fof(f1080,plain,(
% 1.86/0.65    spl4_74 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 1.86/0.65  fof(f997,plain,(
% 1.86/0.65    spl4_65 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.86/0.65  fof(f1035,plain,(
% 1.86/0.65    spl4_70 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 1.86/0.65  fof(f1072,plain,(
% 1.86/0.65    ~v1_relat_1(k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_70),
% 1.86/0.65    inference(resolution,[],[f1037,f46])).
% 1.86/0.65  fof(f46,plain,(
% 1.86/0.65    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 1.86/0.65    inference(cnf_transformation,[],[f27])).
% 1.86/0.65  fof(f27,plain,(
% 1.86/0.65    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.86/0.65    inference(flattening,[],[f26])).
% 1.86/0.65  fof(f26,plain,(
% 1.86/0.65    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.86/0.65    inference(ennf_transformation,[],[f13])).
% 1.86/0.65  fof(f13,axiom,(
% 1.86/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.86/0.65  fof(f1037,plain,(
% 1.86/0.65    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_70),
% 1.86/0.65    inference(avatar_component_clause,[],[f1035])).
% 1.86/0.65  fof(f1045,plain,(
% 1.86/0.65    ~spl4_3 | spl4_65),
% 1.86/0.65    inference(avatar_contradiction_clause,[],[f1044])).
% 1.86/0.65  fof(f1044,plain,(
% 1.86/0.65    $false | (~spl4_3 | spl4_65)),
% 1.86/0.65    inference(resolution,[],[f999,f89])).
% 1.86/0.65  fof(f999,plain,(
% 1.86/0.65    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_65),
% 1.86/0.65    inference(avatar_component_clause,[],[f997])).
% 1.86/0.65  fof(f1038,plain,(
% 1.86/0.65    spl4_70 | ~spl4_3 | ~spl4_37),
% 1.86/0.65    inference(avatar_split_clause,[],[f1019,f489,f85,f1035])).
% 1.86/0.65  fof(f489,plain,(
% 1.86/0.65    spl4_37 <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.86/0.65  fof(f1019,plain,(
% 1.86/0.65    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_3 | ~spl4_37)),
% 1.86/0.65    inference(resolution,[],[f883,f491])).
% 1.86/0.65  fof(f491,plain,(
% 1.86/0.65    r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_37),
% 1.86/0.65    inference(avatar_component_clause,[],[f489])).
% 1.86/0.65  fof(f883,plain,(
% 1.86/0.65    ( ! [X8,X9] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X8)),X9) | r1_tarski(k2_relat_1(k2_wellord1(sK2,X8)),X9)) ) | ~spl4_3),
% 1.86/0.65    inference(superposition,[],[f264,f205])).
% 1.86/0.65  fof(f205,plain,(
% 1.86/0.65    ( ! [X0] : (k3_relat_1(k2_wellord1(sK2,X0)) = k3_tarski(k5_enumset1(k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k2_relat_1(k2_wellord1(sK2,X0))))) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f69,f89])).
% 1.86/0.65  fof(f69,plain,(
% 1.86/0.65    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.86/0.65    inference(definition_unfolding,[],[f41,f68])).
% 1.86/0.65  fof(f68,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.86/0.65    inference(definition_unfolding,[],[f42,f67])).
% 1.86/0.65  fof(f67,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.86/0.65    inference(definition_unfolding,[],[f43,f66])).
% 1.86/0.65  fof(f66,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.86/0.65    inference(definition_unfolding,[],[f54,f65])).
% 1.86/0.65  fof(f65,plain,(
% 1.86/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.86/0.65    inference(definition_unfolding,[],[f61,f64])).
% 1.86/0.65  fof(f64,plain,(
% 1.86/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.86/0.65    inference(definition_unfolding,[],[f62,f63])).
% 1.86/0.65  fof(f63,plain,(
% 1.86/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f10])).
% 1.86/0.65  fof(f10,axiom,(
% 1.86/0.65    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.86/0.65  fof(f62,plain,(
% 1.86/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f9])).
% 1.86/0.65  fof(f9,axiom,(
% 1.86/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.86/0.65  fof(f61,plain,(
% 1.86/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f8])).
% 1.86/0.65  fof(f8,axiom,(
% 1.86/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.86/0.65  fof(f54,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f7])).
% 1.86/0.65  fof(f7,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.86/0.65  fof(f43,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f6])).
% 1.86/0.65  fof(f6,axiom,(
% 1.86/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.86/0.65  fof(f42,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f11])).
% 1.86/0.65  fof(f11,axiom,(
% 1.86/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.86/0.65  fof(f41,plain,(
% 1.86/0.65    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f23])).
% 1.86/0.65  fof(f23,plain,(
% 1.86/0.65    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.86/0.65    inference(ennf_transformation,[],[f12])).
% 1.86/0.65  fof(f12,axiom,(
% 1.86/0.65    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.86/0.65  fof(f264,plain,(
% 1.86/0.65    ( ! [X6,X8,X7] : (~r1_tarski(k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X7)),X8) | r1_tarski(X7,X8)) )),
% 1.86/0.65    inference(resolution,[],[f197,f60])).
% 1.86/0.65  fof(f60,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f37])).
% 1.86/0.65  fof(f37,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.86/0.65    inference(flattening,[],[f36])).
% 1.86/0.65  fof(f36,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.86/0.65    inference(ennf_transformation,[],[f5])).
% 1.86/0.65  fof(f5,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.86/0.65  fof(f197,plain,(
% 1.86/0.65    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))) )),
% 1.86/0.65    inference(resolution,[],[f70,f72])).
% 1.86/0.65  fof(f72,plain,(
% 1.86/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.86/0.65    inference(equality_resolution,[],[f49])).
% 1.86/0.65  fof(f49,plain,(
% 1.86/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.86/0.65    inference(cnf_transformation,[],[f2])).
% 1.86/0.65  fof(f2,axiom,(
% 1.86/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.86/0.65  fof(f70,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))) )),
% 1.86/0.65    inference(definition_unfolding,[],[f58,f68])).
% 1.86/0.65  fof(f58,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f34])).
% 1.86/0.65  fof(f34,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.86/0.65    inference(ennf_transformation,[],[f3])).
% 1.86/0.65  fof(f3,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.86/0.65  fof(f1000,plain,(
% 1.86/0.65    spl4_64 | ~spl4_65 | ~spl4_61),
% 1.86/0.65    inference(avatar_split_clause,[],[f985,f962,f997,f993])).
% 1.86/0.65  fof(f962,plain,(
% 1.86/0.65    spl4_61 <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.86/0.65  fof(f985,plain,(
% 1.86/0.65    ~v1_relat_1(k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl4_61),
% 1.86/0.65    inference(resolution,[],[f964,f47])).
% 1.86/0.65  fof(f47,plain,(
% 1.86/0.65    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.86/0.65    inference(cnf_transformation,[],[f29])).
% 1.86/0.65  fof(f29,plain,(
% 1.86/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.86/0.65    inference(flattening,[],[f28])).
% 1.86/0.65  fof(f28,plain,(
% 1.86/0.65    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.86/0.65    inference(ennf_transformation,[],[f14])).
% 1.86/0.65  fof(f14,axiom,(
% 1.86/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.86/0.65  fof(f964,plain,(
% 1.86/0.65    r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_61),
% 1.86/0.65    inference(avatar_component_clause,[],[f962])).
% 1.86/0.65  fof(f965,plain,(
% 1.86/0.65    spl4_61 | ~spl4_3 | ~spl4_37),
% 1.86/0.65    inference(avatar_split_clause,[],[f946,f489,f85,f962])).
% 1.86/0.65  fof(f946,plain,(
% 1.86/0.65    r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_3 | ~spl4_37)),
% 1.86/0.65    inference(resolution,[],[f878,f491])).
% 1.86/0.65  fof(f878,plain,(
% 1.86/0.65    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) | r1_tarski(k1_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl4_3),
% 1.86/0.65    inference(superposition,[],[f71,f205])).
% 1.86/0.65  fof(f71,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.86/0.65    inference(definition_unfolding,[],[f59,f68])).
% 1.86/0.65  fof(f59,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f35])).
% 1.86/0.65  fof(f35,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.86/0.65    inference(ennf_transformation,[],[f4])).
% 1.86/0.65  fof(f4,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.86/0.65  fof(f492,plain,(
% 1.86/0.65    spl4_37 | ~spl4_2 | ~spl4_3),
% 1.86/0.65    inference(avatar_split_clause,[],[f469,f85,f80,f489])).
% 1.86/0.65  fof(f80,plain,(
% 1.86/0.65    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.86/0.65  fof(f469,plain,(
% 1.86/0.65    r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_2 | ~spl4_3)),
% 1.86/0.65    inference(resolution,[],[f420,f82])).
% 1.86/0.65  fof(f82,plain,(
% 1.86/0.65    r1_tarski(sK0,sK1) | ~spl4_2),
% 1.86/0.65    inference(avatar_component_clause,[],[f80])).
% 1.86/0.65  fof(f420,plain,(
% 1.86/0.65    ( ! [X4,X5] : (~r1_tarski(X4,X5) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X5)) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f417,f60])).
% 1.86/0.65  fof(f417,plain,(
% 1.86/0.65    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl4_3),
% 1.86/0.65    inference(duplicate_literal_removal,[],[f410])).
% 1.86/0.65  fof(f410,plain,(
% 1.86/0.65    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f281,f53])).
% 1.86/0.65  fof(f53,plain,(
% 1.86/0.65    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f30])).
% 1.86/0.65  fof(f30,plain,(
% 1.86/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.86/0.65    inference(ennf_transformation,[],[f1])).
% 1.86/0.65  fof(f1,axiom,(
% 1.86/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.86/0.65  fof(f281,plain,(
% 1.86/0.65    ( ! [X0,X1] : (r2_hidden(sK3(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f146,f87])).
% 1.86/0.65  fof(f146,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2)) )),
% 1.86/0.65    inference(resolution,[],[f57,f52])).
% 1.86/0.65  fof(f52,plain,(
% 1.86/0.65    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f30])).
% 1.86/0.65  fof(f57,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2) | r2_hidden(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f33])).
% 1.86/0.65  fof(f33,plain,(
% 1.86/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 1.86/0.65    inference(flattening,[],[f32])).
% 1.86/0.65  fof(f32,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.65    inference(ennf_transformation,[],[f17])).
% 1.86/0.65  fof(f17,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 1.86/0.65  fof(f253,plain,(
% 1.86/0.65    ~spl4_19 | spl4_1 | ~spl4_3),
% 1.86/0.65    inference(avatar_split_clause,[],[f240,f85,f75,f249])).
% 1.86/0.65  fof(f249,plain,(
% 1.86/0.65    spl4_19 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.86/0.65  fof(f75,plain,(
% 1.86/0.65    spl4_1 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.86/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.86/0.65  fof(f240,plain,(
% 1.86/0.65    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | (spl4_1 | ~spl4_3)),
% 1.86/0.65    inference(superposition,[],[f77,f172])).
% 1.86/0.65  fof(f172,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) ) | ~spl4_3),
% 1.86/0.65    inference(resolution,[],[f55,f87])).
% 1.86/0.65  fof(f55,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f31])).
% 1.86/0.65  fof(f31,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.86/0.65    inference(ennf_transformation,[],[f18])).
% 1.86/0.65  fof(f18,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 1.86/0.65  fof(f77,plain,(
% 1.86/0.65    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) | spl4_1),
% 1.86/0.65    inference(avatar_component_clause,[],[f75])).
% 1.86/0.65  fof(f88,plain,(
% 1.86/0.65    spl4_3),
% 1.86/0.65    inference(avatar_split_clause,[],[f38,f85])).
% 1.86/0.65  fof(f38,plain,(
% 1.86/0.65    v1_relat_1(sK2)),
% 1.86/0.65    inference(cnf_transformation,[],[f22])).
% 1.86/0.65  fof(f22,plain,(
% 1.86/0.65    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.86/0.65    inference(flattening,[],[f21])).
% 1.86/0.65  fof(f21,plain,(
% 1.86/0.65    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.86/0.65    inference(ennf_transformation,[],[f20])).
% 1.86/0.65  fof(f20,negated_conjecture,(
% 1.86/0.65    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.86/0.65    inference(negated_conjecture,[],[f19])).
% 1.86/0.65  fof(f19,conjecture,(
% 1.86/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.86/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 1.86/0.65  fof(f83,plain,(
% 1.86/0.65    spl4_2),
% 1.86/0.65    inference(avatar_split_clause,[],[f39,f80])).
% 1.86/0.65  fof(f39,plain,(
% 1.86/0.65    r1_tarski(sK0,sK1)),
% 1.86/0.65    inference(cnf_transformation,[],[f22])).
% 1.86/0.65  fof(f78,plain,(
% 1.86/0.65    ~spl4_1),
% 1.86/0.65    inference(avatar_split_clause,[],[f40,f75])).
% 1.86/0.65  fof(f40,plain,(
% 1.86/0.65    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.86/0.65    inference(cnf_transformation,[],[f22])).
% 1.86/0.65  % SZS output end Proof for theBenchmark
% 1.86/0.65  % (1907)------------------------------
% 1.86/0.65  % (1907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.65  % (1907)Termination reason: Refutation
% 1.86/0.65  
% 1.86/0.65  % (1907)Memory used [KB]: 12153
% 1.86/0.65  % (1907)Time elapsed: 0.192 s
% 1.86/0.65  % (1907)------------------------------
% 1.86/0.65  % (1907)------------------------------
% 1.86/0.65  % (1890)Success in time 0.286 s
%------------------------------------------------------------------------------
