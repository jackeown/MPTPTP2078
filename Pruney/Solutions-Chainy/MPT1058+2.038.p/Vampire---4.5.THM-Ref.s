%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:22 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 361 expanded)
%              Number of leaves         :   26 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  298 ( 750 expanded)
%              Number of equality atoms :   65 ( 208 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f564,f615,f908,f1102])).

fof(f1102,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f1101,f608,f96,f101])).

fof(f101,plain,
    ( spl5_3
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f96,plain,
    ( spl5_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f608,plain,
    ( spl5_60
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1101,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f1086,f510])).

fof(f510,plain,(
    ! [X7] : k9_relat_1(k6_relat_1(X7),X7) = X7 ),
    inference(global_subsumption,[],[f195,f479])).

fof(f479,plain,(
    ! [X0] : r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(resolution,[],[f388,f228])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))
      | r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f46,f47,f88,f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f223,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X0)))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f71,f120])).

fof(f120,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f119,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f119,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f113,f49])).

fof(f113,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
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

fof(f47,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f388,plain,(
    ! [X0] : r1_tarski(X0,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0))) ),
    inference(forward_demodulation,[],[f382,f48])).

fof(f382,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) ),
    inference(resolution,[],[f163,f46])).

fof(f163,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0)))) ) ),
    inference(resolution,[],[f59,f88])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f195,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k9_relat_1(k6_relat_1(X2),X2))
      | k9_relat_1(k6_relat_1(X2),X2) = X2 ) ),
    inference(resolution,[],[f185,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f185,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) ),
    inference(superposition,[],[f154,f120])).

fof(f154,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(global_subsumption,[],[f46,f149])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2) ) ),
    inference(resolution,[],[f60,f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f1086,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(superposition,[],[f618,f610])).

fof(f610,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f608])).

fof(f618,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0))
    | ~ spl5_2 ),
    inference(superposition,[],[f616,f257])).

fof(f257,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f84,f98])).

fof(f98,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f616,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(forward_demodulation,[],[f316,f510])).

fof(f316,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1))) ),
    inference(global_subsumption,[],[f46,f315])).

fof(f315,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f310,f48])).

fof(f310,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) ) ),
    inference(resolution,[],[f83,f47])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f61,f82])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f908,plain,(
    spl5_61 ),
    inference(avatar_contradiction_clause,[],[f897])).

fof(f897,plain,
    ( $false
    | spl5_61 ),
    inference(resolution,[],[f896,f614])).

fof(f614,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | spl5_61 ),
    inference(avatar_component_clause,[],[f612])).

fof(f612,plain,
    ( spl5_61
  <=> r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f896,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(duplicate_literal_removal,[],[f889])).

fof(f889,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(resolution,[],[f462,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f462,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(global_subsumption,[],[f46,f461])).

fof(f461,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f456,f48])).

fof(f456,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(resolution,[],[f178,f47])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),X2) ) ),
    inference(resolution,[],[f87,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f615,plain,
    ( spl5_60
    | ~ spl5_61
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f591,f335,f612,f608])).

fof(f335,plain,
    ( spl5_31
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f591,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_31 ),
    inference(resolution,[],[f337,f64])).

fof(f337,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f335])).

fof(f564,plain,
    ( spl5_31
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f559,f106,f335])).

fof(f106,plain,
    ( spl5_4
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f559,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f525,f108])).

fof(f108,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(global_subsumption,[],[f46,f47,f88,f524])).

fof(f524,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(forward_demodulation,[],[f522,f48])).

fof(f522,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f70,f510])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f109,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f104,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f43,f101])).

fof(f43,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31500)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (31501)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (31498)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (31515)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (31495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (31488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (31493)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (31510)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (31499)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (31503)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (31502)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (31489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (31517)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (31508)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (31511)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (31505)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (31494)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (31490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (31492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (31491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (31514)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (31497)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (31509)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (31513)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (31512)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (31506)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (31516)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (31496)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (31504)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.71/0.61  % (31504)Refutation found. Thanks to Tanya!
% 1.71/0.61  % SZS status Theorem for theBenchmark
% 1.71/0.61  % SZS output start Proof for theBenchmark
% 1.71/0.61  fof(f1116,plain,(
% 1.71/0.61    $false),
% 1.71/0.61    inference(avatar_sat_refutation,[],[f99,f104,f109,f564,f615,f908,f1102])).
% 1.71/0.61  fof(f1102,plain,(
% 1.71/0.61    spl5_3 | ~spl5_2 | ~spl5_60),
% 1.71/0.61    inference(avatar_split_clause,[],[f1101,f608,f96,f101])).
% 1.71/0.61  fof(f101,plain,(
% 1.71/0.61    spl5_3 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.71/0.61  fof(f96,plain,(
% 1.71/0.61    spl5_2 <=> v1_relat_1(sK0)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.71/0.61  fof(f608,plain,(
% 1.71/0.61    spl5_60 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 1.71/0.61  fof(f1101,plain,(
% 1.71/0.61    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl5_2 | ~spl5_60)),
% 1.71/0.61    inference(forward_demodulation,[],[f1086,f510])).
% 1.71/0.61  fof(f510,plain,(
% 1.71/0.61    ( ! [X7] : (k9_relat_1(k6_relat_1(X7),X7) = X7) )),
% 1.71/0.61    inference(global_subsumption,[],[f195,f479])).
% 1.71/0.61  fof(f479,plain,(
% 1.71/0.61    ( ! [X0] : (r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0))) )),
% 1.71/0.61    inference(resolution,[],[f388,f228])).
% 1.71/0.61  fof(f228,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) | r1_tarski(X0,X1)) )),
% 1.71/0.61    inference(global_subsumption,[],[f46,f47,f88,f227])).
% 1.71/0.61  fof(f227,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,X1)) )),
% 1.71/0.61    inference(forward_demodulation,[],[f223,f49])).
% 1.71/0.61  fof(f49,plain,(
% 1.71/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.71/0.61    inference(cnf_transformation,[],[f12])).
% 1.71/0.61  fof(f12,axiom,(
% 1.71/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.71/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.71/0.61  fof(f223,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,k2_relat_1(k6_relat_1(X0))) | r1_tarski(X0,X1)) )),
% 1.71/0.61    inference(superposition,[],[f71,f120])).
% 1.71/0.61  fof(f120,plain,(
% 1.71/0.61    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.71/0.61    inference(forward_demodulation,[],[f119,f48])).
% 1.71/0.61  fof(f48,plain,(
% 1.71/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.71/0.61    inference(cnf_transformation,[],[f12])).
% 1.71/0.61  fof(f119,plain,(
% 1.71/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.71/0.61    inference(forward_demodulation,[],[f113,f49])).
% 1.71/0.61  fof(f113,plain,(
% 1.71/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 1.71/0.61    inference(resolution,[],[f50,f46])).
% 1.71/0.61  fof(f50,plain,(
% 1.71/0.61    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f25])).
% 1.71/0.62  fof(f25,plain,(
% 1.71/0.62    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.62    inference(ennf_transformation,[],[f11])).
% 1.71/0.62  fof(f11,axiom,(
% 1.71/0.62    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.71/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.71/0.62  fof(f71,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k2_relat_1(X2)) | r1_tarski(X0,X1)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f39])).
% 1.71/0.62  fof(f39,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.71/0.62    inference(flattening,[],[f38])).
% 1.71/0.62  fof(f38,plain,(
% 1.71/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.71/0.62    inference(ennf_transformation,[],[f19])).
% 1.71/0.62  fof(f19,axiom,(
% 1.71/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.71/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.71/0.62  fof(f88,plain,(
% 1.71/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.71/0.62    inference(equality_resolution,[],[f63])).
% 1.71/0.62  fof(f63,plain,(
% 1.71/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.71/0.62    inference(cnf_transformation,[],[f2])).
% 1.71/0.62  fof(f2,axiom,(
% 1.71/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.62  fof(f47,plain,(
% 1.71/0.62    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f14])).
% 1.71/0.62  fof(f14,axiom,(
% 1.71/0.62    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.71/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.71/0.62  fof(f46,plain,(
% 1.71/0.62    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f14])).
% 1.71/0.62  fof(f388,plain,(
% 1.71/0.62    ( ! [X0] : (r1_tarski(X0,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)))) )),
% 1.71/0.62    inference(forward_demodulation,[],[f382,f48])).
% 1.71/0.62  fof(f382,plain,(
% 1.71/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))))) )),
% 1.71/0.62    inference(resolution,[],[f163,f46])).
% 1.71/0.62  fof(f163,plain,(
% 1.71/0.62    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0))))) )),
% 1.71/0.62    inference(resolution,[],[f59,f88])).
% 1.71/0.62  fof(f59,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f29])).
% 1.71/0.62  fof(f29,plain,(
% 1.71/0.62    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(flattening,[],[f28])).
% 1.71/0.62  fof(f28,plain,(
% 1.71/0.62    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(ennf_transformation,[],[f17])).
% 1.71/0.62  fof(f17,axiom,(
% 1.71/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.71/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.71/0.62  fof(f195,plain,(
% 1.71/0.62    ( ! [X2] : (~r1_tarski(X2,k9_relat_1(k6_relat_1(X2),X2)) | k9_relat_1(k6_relat_1(X2),X2) = X2) )),
% 1.71/0.62    inference(resolution,[],[f185,f64])).
% 1.71/0.62  fof(f64,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.71/0.62    inference(cnf_transformation,[],[f2])).
% 1.71/0.62  fof(f185,plain,(
% 1.71/0.62    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0)) )),
% 1.71/0.62    inference(superposition,[],[f154,f120])).
% 1.71/0.62  fof(f154,plain,(
% 1.71/0.62    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2)) )),
% 1.71/0.62    inference(global_subsumption,[],[f46,f149])).
% 1.71/0.62  fof(f149,plain,(
% 1.71/0.62    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2)) )),
% 1.71/0.62    inference(resolution,[],[f60,f47])).
% 1.71/0.62  fof(f60,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f31])).
% 1.71/0.62  fof(f31,plain,(
% 1.71/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(flattening,[],[f30])).
% 1.71/0.62  fof(f30,plain,(
% 1.71/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.71/0.62    inference(ennf_transformation,[],[f16])).
% 1.71/0.62  fof(f16,axiom,(
% 1.71/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.71/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.71/0.62  fof(f1086,plain,(
% 1.71/0.62    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | (~spl5_2 | ~spl5_60)),
% 1.71/0.62    inference(superposition,[],[f618,f610])).
% 1.71/0.62  fof(f610,plain,(
% 1.71/0.62    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_60),
% 1.71/0.62    inference(avatar_component_clause,[],[f608])).
% 1.71/0.62  fof(f618,plain,(
% 1.71/0.62    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0))) ) | ~spl5_2),
% 1.71/0.62    inference(superposition,[],[f616,f257])).
% 1.71/0.62  fof(f257,plain,(
% 1.71/0.62    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl5_2),
% 1.71/0.62    inference(resolution,[],[f84,f98])).
% 1.71/0.62  fof(f98,plain,(
% 1.71/0.62    v1_relat_1(sK0) | ~spl5_2),
% 1.71/0.62    inference(avatar_component_clause,[],[f96])).
% 1.71/0.62  fof(f84,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 1.71/0.62    inference(definition_unfolding,[],[f69,f82])).
% 1.71/0.62  fof(f82,plain,(
% 1.71/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.71/0.62    inference(definition_unfolding,[],[f57,f81])).
% 1.71/0.62  fof(f81,plain,(
% 1.71/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.71/0.62    inference(definition_unfolding,[],[f58,f80])).
% 1.71/0.62  fof(f80,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.71/0.62    inference(definition_unfolding,[],[f68,f79])).
% 2.08/0.63  fof(f79,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f73,f78])).
% 2.08/0.63  fof(f78,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f74,f77])).
% 2.08/0.63  fof(f77,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.63    inference(definition_unfolding,[],[f75,f76])).
% 2.08/0.63  fof(f76,plain,(
% 2.08/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f9])).
% 2.08/0.63  fof(f9,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.08/0.63  fof(f75,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f8])).
% 2.08/0.63  fof(f8,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.08/0.63  fof(f74,plain,(
% 2.08/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f7])).
% 2.08/0.63  fof(f7,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.08/0.63  fof(f73,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f6])).
% 2.08/0.63  fof(f6,axiom,(
% 2.08/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.08/0.63  fof(f68,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f5])).
% 2.08/0.63  fof(f5,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.08/0.63  fof(f58,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f4])).
% 2.08/0.63  fof(f4,axiom,(
% 2.08/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.08/0.63  fof(f57,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f10])).
% 2.08/0.63  fof(f10,axiom,(
% 2.08/0.63    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.08/0.63  fof(f69,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f35])).
% 2.08/0.63  fof(f35,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.08/0.63    inference(ennf_transformation,[],[f15])).
% 2.08/0.63  fof(f15,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.08/0.63  fof(f616,plain,(
% 2.08/0.63    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) )),
% 2.08/0.63    inference(forward_demodulation,[],[f316,f510])).
% 2.08/0.63  fof(f316,plain,(
% 2.08/0.63    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1)))) )),
% 2.08/0.63    inference(global_subsumption,[],[f46,f315])).
% 2.08/0.63  fof(f315,plain,(
% 2.08/0.63    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.08/0.63    inference(forward_demodulation,[],[f310,f48])).
% 2.08/0.63  fof(f310,plain,(
% 2.08/0.63    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))))) )),
% 2.08/0.63    inference(resolution,[],[f83,f47])).
% 2.08/0.63  fof(f83,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 2.08/0.63    inference(definition_unfolding,[],[f61,f82])).
% 2.08/0.63  fof(f61,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f33])).
% 2.08/0.63  fof(f33,plain,(
% 2.08/0.63    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.08/0.63    inference(flattening,[],[f32])).
% 2.08/0.63  fof(f32,plain,(
% 2.08/0.63    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.08/0.63    inference(ennf_transformation,[],[f18])).
% 2.08/0.63  fof(f18,axiom,(
% 2.08/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 2.08/0.63  fof(f908,plain,(
% 2.08/0.63    spl5_61),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f897])).
% 2.08/0.63  fof(f897,plain,(
% 2.08/0.63    $false | spl5_61),
% 2.08/0.63    inference(resolution,[],[f896,f614])).
% 2.08/0.63  fof(f614,plain,(
% 2.08/0.63    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | spl5_61),
% 2.08/0.63    inference(avatar_component_clause,[],[f612])).
% 2.08/0.63  fof(f612,plain,(
% 2.08/0.63    spl5_61 <=> r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 2.08/0.63  fof(f896,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.08/0.63    inference(duplicate_literal_removal,[],[f889])).
% 2.08/0.63  fof(f889,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.08/0.63    inference(resolution,[],[f462,f67])).
% 2.08/0.63  fof(f67,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f34])).
% 2.08/0.63  fof(f34,plain,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f1])).
% 2.08/0.63  fof(f1,axiom,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.08/0.63  fof(f462,plain,(
% 2.08/0.63    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.08/0.63    inference(global_subsumption,[],[f46,f461])).
% 2.08/0.63  fof(f461,plain,(
% 2.08/0.63    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.08/0.63    inference(forward_demodulation,[],[f456,f48])).
% 2.08/0.63  fof(f456,plain,(
% 2.08/0.63    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.08/0.63    inference(resolution,[],[f178,f47])).
% 2.08/0.63  fof(f178,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),X2)) )),
% 2.08/0.63    inference(resolution,[],[f87,f66])).
% 2.08/0.63  fof(f66,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f34])).
% 2.08/0.63  fof(f87,plain,(
% 2.08/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.08/0.63    inference(equality_resolution,[],[f54])).
% 2.08/0.63  fof(f54,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.08/0.63    inference(cnf_transformation,[],[f27])).
% 2.08/0.63  fof(f27,plain,(
% 2.08/0.63    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.63    inference(flattening,[],[f26])).
% 2.08/0.63  fof(f26,plain,(
% 2.08/0.63    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f13])).
% 2.08/0.63  fof(f13,axiom,(
% 2.08/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 2.08/0.63  fof(f615,plain,(
% 2.08/0.63    spl5_60 | ~spl5_61 | ~spl5_31),
% 2.08/0.63    inference(avatar_split_clause,[],[f591,f335,f612,f608])).
% 2.08/0.63  fof(f335,plain,(
% 2.08/0.63    spl5_31 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.08/0.63  fof(f591,plain,(
% 2.08/0.63    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_31),
% 2.08/0.63    inference(resolution,[],[f337,f64])).
% 2.08/0.63  fof(f337,plain,(
% 2.08/0.63    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl5_31),
% 2.08/0.63    inference(avatar_component_clause,[],[f335])).
% 2.08/0.63  fof(f564,plain,(
% 2.08/0.63    spl5_31 | ~spl5_4),
% 2.08/0.63    inference(avatar_split_clause,[],[f559,f106,f335])).
% 2.08/0.63  fof(f106,plain,(
% 2.08/0.63    spl5_4 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.08/0.63  fof(f559,plain,(
% 2.08/0.63    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl5_4),
% 2.08/0.63    inference(resolution,[],[f525,f108])).
% 2.08/0.63  fof(f108,plain,(
% 2.08/0.63    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl5_4),
% 2.08/0.63    inference(avatar_component_clause,[],[f106])).
% 2.08/0.63  fof(f525,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.08/0.63    inference(global_subsumption,[],[f46,f47,f88,f524])).
% 2.08/0.63  fof(f524,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.08/0.63    inference(forward_demodulation,[],[f522,f48])).
% 2.08/0.63  fof(f522,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_funct_1(k6_relat_1(X0)) | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.08/0.63    inference(superposition,[],[f70,f510])).
% 2.08/0.63  fof(f70,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f37])).
% 2.08/0.63  fof(f37,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.08/0.63    inference(flattening,[],[f36])).
% 2.08/0.63  fof(f36,plain,(
% 2.08/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.08/0.63    inference(ennf_transformation,[],[f20])).
% 2.08/0.63  fof(f20,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 2.08/0.63  fof(f109,plain,(
% 2.08/0.63    spl5_4),
% 2.08/0.63    inference(avatar_split_clause,[],[f42,f106])).
% 2.08/0.63  fof(f42,plain,(
% 2.08/0.63    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.08/0.63    inference(cnf_transformation,[],[f24])).
% 2.08/0.63  fof(f24,plain,(
% 2.08/0.63    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.08/0.63    inference(flattening,[],[f23])).
% 2.08/0.63  fof(f23,plain,(
% 2.08/0.63    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f22])).
% 2.08/0.63  fof(f22,negated_conjecture,(
% 2.08/0.63    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.08/0.63    inference(negated_conjecture,[],[f21])).
% 2.08/0.63  fof(f21,conjecture,(
% 2.08/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 2.08/0.63  fof(f104,plain,(
% 2.08/0.63    ~spl5_3),
% 2.08/0.63    inference(avatar_split_clause,[],[f43,f101])).
% 2.08/0.63  fof(f43,plain,(
% 2.08/0.63    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f24])).
% 2.08/0.63  fof(f99,plain,(
% 2.08/0.63    spl5_2),
% 2.08/0.63    inference(avatar_split_clause,[],[f44,f96])).
% 2.08/0.63  fof(f44,plain,(
% 2.08/0.63    v1_relat_1(sK0)),
% 2.08/0.63    inference(cnf_transformation,[],[f24])).
% 2.08/0.63  % SZS output end Proof for theBenchmark
% 2.08/0.63  % (31504)------------------------------
% 2.08/0.63  % (31504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (31504)Termination reason: Refutation
% 2.08/0.63  
% 2.08/0.63  % (31504)Memory used [KB]: 11513
% 2.08/0.63  % (31504)Time elapsed: 0.228 s
% 2.08/0.63  % (31504)------------------------------
% 2.08/0.63  % (31504)------------------------------
% 2.08/0.63  % (31487)Success in time 0.278 s
%------------------------------------------------------------------------------
