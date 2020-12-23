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
% DateTime   : Thu Dec  3 13:07:22 EST 2020

% Result     : Theorem 2.90s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 240 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  239 ( 459 expanded)
%              Number of equality atoms :   85 ( 186 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f109,f1295,f1894])).

fof(f1894,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f1893,f523,f89,f94])).

fof(f94,plain,
    ( spl5_3
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f89,plain,
    ( spl5_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f523,plain,
    ( spl5_32
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1893,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f1877,f308])).

fof(f308,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f299,f132])).

fof(f132,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f131,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f131,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f125,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f125,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f299,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(resolution,[],[f188,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(global_subsumption,[],[f40,f41,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(superposition,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1877,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(superposition,[],[f635,f525])).

fof(f525,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f523])).

fof(f635,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0))
    | ~ spl5_2 ),
    inference(superposition,[],[f613,f212])).

fof(f212,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f77,f91])).

fof(f91,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f613,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(forward_demodulation,[],[f273,f308])).

fof(f273,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1))) ),
    inference(global_subsumption,[],[f40,f272])).

fof(f272,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f267,f42])).

fof(f267,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) ) ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f1295,plain,
    ( spl5_32
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1273,f106,f523])).

fof(f106,plain,
    ( spl5_5
  <=> sK1 = k2_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1273,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f1219,f108])).

fof(f108,plain,
    ( sK1 = k2_xboole_0(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1219,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f358,f1175])).

fof(f1175,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) = X1 ),
    inference(resolution,[],[f1118,f136])).

fof(f136,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f58,f112])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f65,f81])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1118,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(superposition,[],[f1109,f358])).

fof(f1109,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(duplicate_literal_removal,[],[f1100])).

fof(f1100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(resolution,[],[f401,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f401,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(global_subsumption,[],[f40,f400])).

fof(f400,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f395,f42])).

fof(f395,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(resolution,[],[f165,f41])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),X2) ) ),
    inference(resolution,[],[f80,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f358,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f196,f132])).

fof(f196,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f109,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f104,f99,f106])).

fof(f99,plain,
    ( spl5_4
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f104,plain,
    ( sK1 = k2_xboole_0(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f53,f101])).

fof(f101,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f99])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f97,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.52  % (21232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (21230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (21251)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (21254)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (21229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (21257)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (21229)Refutation not found, incomplete strategy% (21229)------------------------------
% 0.22/0.56  % (21229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21229)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21229)Memory used [KB]: 1663
% 0.22/0.56  % (21229)Time elapsed: 0.155 s
% 0.22/0.56  % (21229)------------------------------
% 0.22/0.56  % (21229)------------------------------
% 0.22/0.57  % (21253)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (21240)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (21239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (21236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (21239)Refutation not found, incomplete strategy% (21239)------------------------------
% 0.22/0.57  % (21239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (21247)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (21233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (21239)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (21239)Memory used [KB]: 10618
% 0.22/0.57  % (21239)Time elapsed: 0.140 s
% 0.22/0.57  % (21239)------------------------------
% 0.22/0.57  % (21239)------------------------------
% 0.22/0.58  % (21255)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (21247)Refutation not found, incomplete strategy% (21247)------------------------------
% 0.22/0.58  % (21247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (21247)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (21247)Memory used [KB]: 10618
% 0.22/0.58  % (21247)Time elapsed: 0.142 s
% 0.22/0.58  % (21247)------------------------------
% 0.22/0.58  % (21247)------------------------------
% 0.22/0.58  % (21240)Refutation not found, incomplete strategy% (21240)------------------------------
% 0.22/0.58  % (21240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (21240)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (21240)Memory used [KB]: 10618
% 0.22/0.58  % (21240)Time elapsed: 0.153 s
% 0.22/0.58  % (21240)------------------------------
% 0.22/0.58  % (21240)------------------------------
% 0.22/0.58  % (21243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (21258)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (21249)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.59  % (21231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.59  % (21237)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.59  % (21253)Refutation not found, incomplete strategy% (21253)------------------------------
% 0.22/0.59  % (21253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (21253)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (21253)Memory used [KB]: 10746
% 0.22/0.59  % (21253)Time elapsed: 0.188 s
% 0.22/0.59  % (21253)------------------------------
% 0.22/0.59  % (21253)------------------------------
% 0.22/0.60  % (21244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.61  % (21245)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.61  % (21259)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.62  % (21241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.62  % (21256)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.63  % (21234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.96/0.64  % (21238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.96/0.64  % (21238)Refutation not found, incomplete strategy% (21238)------------------------------
% 1.96/0.64  % (21238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (21238)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.64  
% 1.96/0.64  % (21238)Memory used [KB]: 10618
% 1.96/0.64  % (21238)Time elapsed: 0.208 s
% 1.96/0.64  % (21238)------------------------------
% 1.96/0.64  % (21238)------------------------------
% 1.96/0.65  % (21242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.28/0.66  % (21235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.32/0.68  % (21252)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.32/0.69  % (21260)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.32/0.69  % (21250)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.66/0.72  % (21284)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.90/0.76  % (21281)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.90/0.76  % (21281)Refutation not found, incomplete strategy% (21281)------------------------------
% 2.90/0.76  % (21281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.76  % (21281)Termination reason: Refutation not found, incomplete strategy
% 2.90/0.76  
% 2.90/0.76  % (21281)Memory used [KB]: 6140
% 2.90/0.76  % (21281)Time elapsed: 0.153 s
% 2.90/0.76  % (21281)------------------------------
% 2.90/0.76  % (21281)------------------------------
% 2.90/0.77  % (21245)Refutation found. Thanks to Tanya!
% 2.90/0.77  % SZS status Theorem for theBenchmark
% 2.90/0.77  % SZS output start Proof for theBenchmark
% 2.90/0.77  fof(f1912,plain,(
% 2.90/0.77    $false),
% 2.90/0.77    inference(avatar_sat_refutation,[],[f92,f97,f102,f109,f1295,f1894])).
% 2.90/0.77  fof(f1894,plain,(
% 2.90/0.77    spl5_3 | ~spl5_2 | ~spl5_32),
% 2.90/0.77    inference(avatar_split_clause,[],[f1893,f523,f89,f94])).
% 2.90/0.77  fof(f94,plain,(
% 2.90/0.77    spl5_3 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.90/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.90/0.77  fof(f89,plain,(
% 2.90/0.77    spl5_2 <=> v1_relat_1(sK0)),
% 2.90/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.90/0.77  fof(f523,plain,(
% 2.90/0.77    spl5_32 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 2.90/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.90/0.77  fof(f1893,plain,(
% 2.90/0.77    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl5_2 | ~spl5_32)),
% 2.90/0.77    inference(forward_demodulation,[],[f1877,f308])).
% 2.90/0.77  fof(f308,plain,(
% 2.90/0.77    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.90/0.77    inference(forward_demodulation,[],[f299,f132])).
% 2.90/0.77  fof(f132,plain,(
% 2.90/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.90/0.77    inference(forward_demodulation,[],[f131,f42])).
% 2.90/0.77  fof(f42,plain,(
% 2.90/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.90/0.77    inference(cnf_transformation,[],[f14])).
% 2.90/0.77  fof(f14,axiom,(
% 2.90/0.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.90/0.77  fof(f131,plain,(
% 2.90/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.90/0.77    inference(forward_demodulation,[],[f125,f43])).
% 2.90/0.77  fof(f43,plain,(
% 2.90/0.77    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.90/0.77    inference(cnf_transformation,[],[f14])).
% 2.90/0.77  fof(f125,plain,(
% 2.90/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.90/0.77    inference(resolution,[],[f44,f40])).
% 2.90/0.77  fof(f40,plain,(
% 2.90/0.77    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.90/0.77    inference(cnf_transformation,[],[f16])).
% 2.90/0.77  fof(f16,axiom,(
% 2.90/0.77    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.90/0.77  fof(f44,plain,(
% 2.90/0.77    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f24])).
% 2.90/0.77  fof(f24,plain,(
% 2.90/0.77    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.77    inference(ennf_transformation,[],[f12])).
% 2.90/0.77  fof(f12,axiom,(
% 2.90/0.77    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.90/0.77  fof(f299,plain,(
% 2.90/0.77    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0) )),
% 2.90/0.77    inference(resolution,[],[f188,f81])).
% 2.90/0.77  fof(f81,plain,(
% 2.90/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.90/0.77    inference(equality_resolution,[],[f57])).
% 2.90/0.77  fof(f57,plain,(
% 2.90/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.90/0.77    inference(cnf_transformation,[],[f2])).
% 2.90/0.77  fof(f2,axiom,(
% 2.90/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.90/0.77  fof(f188,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 2.90/0.77    inference(global_subsumption,[],[f40,f41,f187])).
% 2.90/0.77  fof(f187,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 2.90/0.77    inference(superposition,[],[f55,f43])).
% 2.90/0.77  fof(f55,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 2.90/0.77    inference(cnf_transformation,[],[f31])).
% 2.90/0.77  fof(f31,plain,(
% 2.90/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.90/0.77    inference(flattening,[],[f30])).
% 2.90/0.77  fof(f30,plain,(
% 2.90/0.77    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.90/0.77    inference(ennf_transformation,[],[f18])).
% 2.90/0.77  fof(f18,axiom,(
% 2.90/0.77    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.90/0.77  fof(f41,plain,(
% 2.90/0.77    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.90/0.77    inference(cnf_transformation,[],[f16])).
% 2.90/0.77  fof(f1877,plain,(
% 2.90/0.77    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | (~spl5_2 | ~spl5_32)),
% 2.90/0.77    inference(superposition,[],[f635,f525])).
% 2.90/0.77  fof(f525,plain,(
% 2.90/0.77    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_32),
% 2.90/0.77    inference(avatar_component_clause,[],[f523])).
% 2.90/0.77  fof(f635,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0))) ) | ~spl5_2),
% 2.90/0.77    inference(superposition,[],[f613,f212])).
% 2.90/0.77  fof(f212,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl5_2),
% 2.90/0.77    inference(resolution,[],[f77,f91])).
% 2.90/0.77  fof(f91,plain,(
% 2.90/0.77    v1_relat_1(sK0) | ~spl5_2),
% 2.90/0.77    inference(avatar_component_clause,[],[f89])).
% 2.90/0.77  fof(f77,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 2.90/0.77    inference(definition_unfolding,[],[f63,f75])).
% 2.90/0.77  fof(f75,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.90/0.77    inference(definition_unfolding,[],[f51,f74])).
% 2.90/0.77  fof(f74,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.90/0.77    inference(definition_unfolding,[],[f52,f73])).
% 2.90/0.77  fof(f73,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.90/0.77    inference(definition_unfolding,[],[f62,f72])).
% 2.90/0.77  fof(f72,plain,(
% 2.90/0.77    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.90/0.77    inference(definition_unfolding,[],[f66,f71])).
% 2.90/0.77  fof(f71,plain,(
% 2.90/0.77    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.90/0.77    inference(definition_unfolding,[],[f67,f70])).
% 2.90/0.77  fof(f70,plain,(
% 2.90/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.90/0.77    inference(definition_unfolding,[],[f68,f69])).
% 2.90/0.77  fof(f69,plain,(
% 2.90/0.77    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f10])).
% 2.90/0.77  fof(f10,axiom,(
% 2.90/0.77    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.90/0.77  fof(f68,plain,(
% 2.90/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f9])).
% 2.90/0.77  fof(f9,axiom,(
% 2.90/0.77    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.90/0.77  fof(f67,plain,(
% 2.90/0.77    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f8])).
% 2.90/0.77  fof(f8,axiom,(
% 2.90/0.77    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.90/0.77  fof(f66,plain,(
% 2.90/0.77    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f7])).
% 2.90/0.77  fof(f7,axiom,(
% 2.90/0.77    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.90/0.77  fof(f62,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f6])).
% 2.90/0.77  fof(f6,axiom,(
% 2.90/0.77    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.90/0.77  fof(f52,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f5])).
% 2.90/0.77  fof(f5,axiom,(
% 2.90/0.77    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.90/0.77  fof(f51,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f11])).
% 2.90/0.77  fof(f11,axiom,(
% 2.90/0.77    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.90/0.77  fof(f63,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.90/0.77    inference(cnf_transformation,[],[f33])).
% 2.90/0.77  fof(f33,plain,(
% 2.90/0.77    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.90/0.77    inference(ennf_transformation,[],[f17])).
% 2.90/0.77  fof(f17,axiom,(
% 2.90/0.77    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.90/0.77  fof(f613,plain,(
% 2.90/0.77    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) )),
% 2.90/0.77    inference(forward_demodulation,[],[f273,f308])).
% 2.90/0.77  fof(f273,plain,(
% 2.90/0.77    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1)))) )),
% 2.90/0.77    inference(global_subsumption,[],[f40,f272])).
% 2.90/0.77  fof(f272,plain,(
% 2.90/0.77    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.90/0.77    inference(forward_demodulation,[],[f267,f42])).
% 2.90/0.77  fof(f267,plain,(
% 2.90/0.77    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))))) )),
% 2.90/0.77    inference(resolution,[],[f76,f41])).
% 2.90/0.77  fof(f76,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 2.90/0.77    inference(definition_unfolding,[],[f54,f75])).
% 2.90/0.77  fof(f54,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 2.90/0.77    inference(cnf_transformation,[],[f29])).
% 2.90/0.77  fof(f29,plain,(
% 2.90/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.90/0.77    inference(flattening,[],[f28])).
% 2.90/0.77  fof(f28,plain,(
% 2.90/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.90/0.77    inference(ennf_transformation,[],[f19])).
% 2.90/0.77  fof(f19,axiom,(
% 2.90/0.77    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 2.90/0.77  fof(f1295,plain,(
% 2.90/0.77    spl5_32 | ~spl5_5),
% 2.90/0.77    inference(avatar_split_clause,[],[f1273,f106,f523])).
% 2.90/0.77  fof(f106,plain,(
% 2.90/0.77    spl5_5 <=> sK1 = k2_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 2.90/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.90/0.77  fof(f1273,plain,(
% 2.90/0.77    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_5),
% 2.90/0.77    inference(superposition,[],[f1219,f108])).
% 2.90/0.77  fof(f108,plain,(
% 2.90/0.77    sK1 = k2_xboole_0(k10_relat_1(sK0,sK2),sK1) | ~spl5_5),
% 2.90/0.77    inference(avatar_component_clause,[],[f106])).
% 2.90/0.77  fof(f1219,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = X0) )),
% 2.90/0.77    inference(backward_demodulation,[],[f358,f1175])).
% 2.90/0.77  fof(f1175,plain,(
% 2.90/0.77    ( ! [X2,X1] : (k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) = X1) )),
% 2.90/0.77    inference(resolution,[],[f1118,f136])).
% 2.90/0.77  fof(f136,plain,(
% 2.90/0.77    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 2.90/0.77    inference(resolution,[],[f58,f112])).
% 2.90/0.77  fof(f112,plain,(
% 2.90/0.77    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.90/0.77    inference(resolution,[],[f65,f81])).
% 2.90/0.77  fof(f65,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f35])).
% 2.90/0.77  fof(f35,plain,(
% 2.90/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.90/0.77    inference(ennf_transformation,[],[f3])).
% 2.90/0.77  fof(f3,axiom,(
% 2.90/0.77    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.90/0.77  fof(f58,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.90/0.77    inference(cnf_transformation,[],[f2])).
% 2.90/0.77  fof(f1118,plain,(
% 2.90/0.77    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)),X1)) )),
% 2.90/0.77    inference(superposition,[],[f1109,f358])).
% 2.90/0.77  fof(f1109,plain,(
% 2.90/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.90/0.77    inference(duplicate_literal_removal,[],[f1100])).
% 2.90/0.77  fof(f1100,plain,(
% 2.90/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.90/0.77    inference(resolution,[],[f401,f61])).
% 2.90/0.77  fof(f61,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f32])).
% 2.90/0.77  fof(f32,plain,(
% 2.90/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.90/0.77    inference(ennf_transformation,[],[f1])).
% 2.90/0.77  fof(f1,axiom,(
% 2.90/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.90/0.77  fof(f401,plain,(
% 2.90/0.77    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.90/0.77    inference(global_subsumption,[],[f40,f400])).
% 2.90/0.77  fof(f400,plain,(
% 2.90/0.77    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.90/0.77    inference(forward_demodulation,[],[f395,f42])).
% 2.90/0.77  fof(f395,plain,(
% 2.90/0.77    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.90/0.77    inference(resolution,[],[f165,f41])).
% 2.90/0.77  fof(f165,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),X2)) )),
% 2.90/0.77    inference(resolution,[],[f80,f60])).
% 2.90/0.77  fof(f60,plain,(
% 2.90/0.77    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.90/0.77    inference(cnf_transformation,[],[f32])).
% 2.90/0.77  fof(f80,plain,(
% 2.90/0.77    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.90/0.77    inference(equality_resolution,[],[f48])).
% 2.90/0.77  fof(f48,plain,(
% 2.90/0.77    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.90/0.77    inference(cnf_transformation,[],[f26])).
% 2.90/0.77  fof(f26,plain,(
% 2.90/0.77    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.77    inference(flattening,[],[f25])).
% 2.90/0.77  fof(f25,plain,(
% 2.90/0.77    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.77    inference(ennf_transformation,[],[f15])).
% 2.90/0.77  fof(f15,axiom,(
% 2.90/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 2.90/0.77  fof(f358,plain,(
% 2.90/0.77    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.90/0.77    inference(superposition,[],[f196,f132])).
% 2.90/0.77  fof(f196,plain,(
% 2.90/0.77    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 2.90/0.77    inference(resolution,[],[f64,f40])).
% 2.90/0.77  fof(f64,plain,(
% 2.90/0.77    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.90/0.77    inference(cnf_transformation,[],[f34])).
% 2.90/0.77  fof(f34,plain,(
% 2.90/0.77    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.90/0.77    inference(ennf_transformation,[],[f13])).
% 2.90/0.77  fof(f13,axiom,(
% 2.90/0.77    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 2.90/0.77  fof(f109,plain,(
% 2.90/0.77    spl5_5 | ~spl5_4),
% 2.90/0.77    inference(avatar_split_clause,[],[f104,f99,f106])).
% 2.90/0.77  fof(f99,plain,(
% 2.90/0.77    spl5_4 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.90/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.90/0.77  fof(f104,plain,(
% 2.90/0.77    sK1 = k2_xboole_0(k10_relat_1(sK0,sK2),sK1) | ~spl5_4),
% 2.90/0.77    inference(resolution,[],[f53,f101])).
% 2.90/0.77  fof(f101,plain,(
% 2.90/0.77    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl5_4),
% 2.90/0.77    inference(avatar_component_clause,[],[f99])).
% 2.90/0.77  fof(f53,plain,(
% 2.90/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.90/0.77    inference(cnf_transformation,[],[f27])).
% 2.90/0.77  fof(f27,plain,(
% 2.90/0.77    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.90/0.77    inference(ennf_transformation,[],[f4])).
% 2.90/0.77  fof(f4,axiom,(
% 2.90/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.90/0.77  fof(f102,plain,(
% 2.90/0.77    spl5_4),
% 2.90/0.77    inference(avatar_split_clause,[],[f36,f99])).
% 2.90/0.77  fof(f36,plain,(
% 2.90/0.77    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.90/0.77    inference(cnf_transformation,[],[f23])).
% 2.90/0.77  fof(f23,plain,(
% 2.90/0.77    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.90/0.77    inference(flattening,[],[f22])).
% 2.90/0.77  fof(f22,plain,(
% 2.90/0.77    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.90/0.77    inference(ennf_transformation,[],[f21])).
% 2.90/0.77  fof(f21,negated_conjecture,(
% 2.90/0.77    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.90/0.77    inference(negated_conjecture,[],[f20])).
% 2.90/0.77  fof(f20,conjecture,(
% 2.90/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.90/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 2.90/0.77  fof(f97,plain,(
% 2.90/0.77    ~spl5_3),
% 2.90/0.77    inference(avatar_split_clause,[],[f37,f94])).
% 2.90/0.77  fof(f37,plain,(
% 2.90/0.77    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.90/0.77    inference(cnf_transformation,[],[f23])).
% 2.90/0.77  fof(f92,plain,(
% 2.90/0.77    spl5_2),
% 2.90/0.77    inference(avatar_split_clause,[],[f38,f89])).
% 2.90/0.77  fof(f38,plain,(
% 2.90/0.77    v1_relat_1(sK0)),
% 2.90/0.77    inference(cnf_transformation,[],[f23])).
% 2.90/0.77  % SZS output end Proof for theBenchmark
% 2.90/0.77  % (21245)------------------------------
% 2.90/0.77  % (21245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.77  % (21245)Termination reason: Refutation
% 2.90/0.77  
% 2.90/0.77  % (21245)Memory used [KB]: 12409
% 2.90/0.77  % (21245)Time elapsed: 0.336 s
% 2.90/0.77  % (21245)------------------------------
% 2.90/0.77  % (21245)------------------------------
% 2.90/0.78  % (21226)Success in time 0.414 s
%------------------------------------------------------------------------------
