%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:22 EST 2020

% Result     : Theorem 2.90s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 238 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  254 ( 492 expanded)
%              Number of equality atoms :   71 ( 169 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1824,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f489,f657,f1007,f1801])).

fof(f1801,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f1800,f650,f94,f99])).

fof(f99,plain,
    ( spl5_3
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f94,plain,
    ( spl5_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f650,plain,
    ( spl5_44
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1800,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1779,f426])).

fof(f426,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f410,f137])).

fof(f137,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f136,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f136,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f130,f47])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f130,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f410,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(resolution,[],[f222,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(global_subsumption,[],[f44,f45,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(superposition,[],[f60,f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f45,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1779,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(superposition,[],[f618,f652])).

fof(f652,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f650])).

fof(f618,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0))
    | ~ spl5_2 ),
    inference(superposition,[],[f608,f270])).

fof(f270,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f82,f96])).

fof(f96,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f608,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(forward_demodulation,[],[f320,f426])).

fof(f320,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1))) ),
    inference(global_subsumption,[],[f44,f319])).

fof(f319,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f314,f46])).

fof(f314,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) ) ),
    inference(resolution,[],[f81,f45])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f1007,plain,(
    spl5_45 ),
    inference(avatar_contradiction_clause,[],[f994])).

fof(f994,plain,
    ( $false
    | spl5_45 ),
    inference(resolution,[],[f993,f656])).

fof(f656,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | spl5_45 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl5_45
  <=> r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f993,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(duplicate_literal_removal,[],[f986])).

fof(f986,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(resolution,[],[f475,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f475,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(global_subsumption,[],[f44,f474])).

fof(f474,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f469,f46])).

fof(f469,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(resolution,[],[f185,f45])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),X2) ) ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f657,plain,
    ( spl5_44
    | ~ spl5_45
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f632,f266,f654,f650])).

fof(f266,plain,
    ( spl5_19
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f632,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_19 ),
    inference(resolution,[],[f268,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f268,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f266])).

fof(f489,plain,
    ( spl5_19
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f481,f104,f266])).

fof(f104,plain,
    ( spl5_4
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f481,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f447,f106])).

fof(f106,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(global_subsumption,[],[f44,f45,f86,f446])).

fof(f446,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(forward_demodulation,[],[f445,f46])).

fof(f445,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f70,f426])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f107,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f102,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f41,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.48/0.56  % (13512)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.56  % (13503)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.57  % (13495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.58  % (13494)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.58  % (13500)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.58  % (13507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.69/0.58  % (13488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.69/0.59  % (13493)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.59  % (13491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.69/0.60  % (13516)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.60  % (13490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.69/0.60  % (13492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.69/0.60  % (13496)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.69/0.61  % (13510)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.69/0.61  % (13510)Refutation not found, incomplete strategy% (13510)------------------------------
% 1.69/0.61  % (13510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (13510)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (13510)Memory used [KB]: 10746
% 1.69/0.61  % (13510)Time elapsed: 0.179 s
% 1.69/0.61  % (13510)------------------------------
% 1.69/0.61  % (13510)------------------------------
% 1.69/0.62  % (13489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.62  % (13505)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.62  % (13505)Refutation not found, incomplete strategy% (13505)------------------------------
% 1.69/0.62  % (13505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (13505)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (13505)Memory used [KB]: 10618
% 1.69/0.62  % (13505)Time elapsed: 0.184 s
% 1.69/0.62  % (13505)------------------------------
% 1.69/0.62  % (13505)------------------------------
% 1.69/0.62  % (13517)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.69/0.62  % (13509)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.69/0.62  % (13498)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.69/0.62  % (13492)Refutation not found, incomplete strategy% (13492)------------------------------
% 1.69/0.62  % (13492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (13492)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (13492)Memory used [KB]: 6268
% 1.69/0.62  % (13492)Time elapsed: 0.187 s
% 1.69/0.62  % (13492)------------------------------
% 1.69/0.62  % (13492)------------------------------
% 1.69/0.63  % (13498)Refutation not found, incomplete strategy% (13498)------------------------------
% 1.69/0.63  % (13498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.63  % (13498)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.63  
% 1.69/0.63  % (13498)Memory used [KB]: 10618
% 1.69/0.63  % (13498)Time elapsed: 0.195 s
% 1.69/0.63  % (13508)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.69/0.63  % (13498)------------------------------
% 1.69/0.63  % (13498)------------------------------
% 1.69/0.63  % (13497)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.69/0.63  % (13513)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.64  % (13504)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.69/0.64  % (13501)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.69/0.64  % (13515)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.69/0.64  % (13502)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.69/0.64  % (13511)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.69/0.65  % (13506)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.23/0.65  % (13497)Refutation not found, incomplete strategy% (13497)------------------------------
% 2.23/0.65  % (13497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.65  % (13497)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.65  
% 2.23/0.65  % (13497)Memory used [KB]: 10746
% 2.23/0.65  % (13497)Time elapsed: 0.202 s
% 2.23/0.65  % (13497)------------------------------
% 2.23/0.65  % (13497)------------------------------
% 2.23/0.66  % (13499)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.23/0.66  % (13499)Refutation not found, incomplete strategy% (13499)------------------------------
% 2.23/0.66  % (13499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.66  % (13499)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.66  
% 2.23/0.66  % (13499)Memory used [KB]: 10618
% 2.23/0.66  % (13499)Time elapsed: 0.227 s
% 2.23/0.66  % (13499)------------------------------
% 2.23/0.66  % (13499)------------------------------
% 2.23/0.66  % (13514)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.90/0.78  % (13559)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.90/0.79  % (13555)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.90/0.79  % (13504)Refutation found. Thanks to Tanya!
% 2.90/0.79  % SZS status Theorem for theBenchmark
% 2.90/0.79  % SZS output start Proof for theBenchmark
% 2.90/0.79  fof(f1824,plain,(
% 2.90/0.79    $false),
% 2.90/0.79    inference(avatar_sat_refutation,[],[f97,f102,f107,f489,f657,f1007,f1801])).
% 2.90/0.79  fof(f1801,plain,(
% 2.90/0.79    spl5_3 | ~spl5_2 | ~spl5_44),
% 2.90/0.79    inference(avatar_split_clause,[],[f1800,f650,f94,f99])).
% 2.90/0.79  fof(f99,plain,(
% 2.90/0.79    spl5_3 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.90/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.90/0.79  fof(f94,plain,(
% 2.90/0.79    spl5_2 <=> v1_relat_1(sK0)),
% 2.90/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.90/0.79  fof(f650,plain,(
% 2.90/0.79    spl5_44 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 2.90/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 2.90/0.79  fof(f1800,plain,(
% 2.90/0.79    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl5_2 | ~spl5_44)),
% 2.90/0.79    inference(forward_demodulation,[],[f1779,f426])).
% 2.90/0.79  fof(f426,plain,(
% 2.90/0.79    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.90/0.79    inference(forward_demodulation,[],[f410,f137])).
% 2.90/0.79  fof(f137,plain,(
% 2.90/0.79    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.90/0.79    inference(forward_demodulation,[],[f136,f46])).
% 2.90/0.79  fof(f46,plain,(
% 2.90/0.79    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.90/0.79    inference(cnf_transformation,[],[f13])).
% 2.90/0.79  fof(f13,axiom,(
% 2.90/0.79    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.90/0.79  fof(f136,plain,(
% 2.90/0.79    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.90/0.79    inference(forward_demodulation,[],[f130,f47])).
% 2.90/0.79  fof(f47,plain,(
% 2.90/0.79    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.90/0.79    inference(cnf_transformation,[],[f13])).
% 2.90/0.79  fof(f130,plain,(
% 2.90/0.79    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.90/0.79    inference(resolution,[],[f48,f44])).
% 2.90/0.79  fof(f44,plain,(
% 2.90/0.79    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.90/0.79    inference(cnf_transformation,[],[f15])).
% 2.90/0.79  fof(f15,axiom,(
% 2.90/0.79    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.90/0.79  fof(f48,plain,(
% 2.90/0.79    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f25])).
% 2.90/0.79  fof(f25,plain,(
% 2.90/0.79    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.79    inference(ennf_transformation,[],[f12])).
% 2.90/0.79  fof(f12,axiom,(
% 2.90/0.79    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.90/0.79  fof(f410,plain,(
% 2.90/0.79    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0) )),
% 2.90/0.79    inference(resolution,[],[f222,f86])).
% 2.90/0.79  fof(f86,plain,(
% 2.90/0.79    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.90/0.79    inference(equality_resolution,[],[f62])).
% 2.90/0.79  fof(f62,plain,(
% 2.90/0.79    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.90/0.79    inference(cnf_transformation,[],[f2])).
% 2.90/0.79  fof(f2,axiom,(
% 2.90/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.90/0.79  fof(f222,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 2.90/0.79    inference(global_subsumption,[],[f44,f45,f216])).
% 2.90/0.79  fof(f216,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 2.90/0.79    inference(superposition,[],[f60,f47])).
% 2.90/0.79  fof(f60,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 2.90/0.79    inference(cnf_transformation,[],[f34])).
% 2.90/0.79  fof(f34,plain,(
% 2.90/0.79    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.90/0.79    inference(flattening,[],[f33])).
% 2.90/0.79  fof(f33,plain,(
% 2.90/0.79    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.90/0.79    inference(ennf_transformation,[],[f18])).
% 2.90/0.79  fof(f18,axiom,(
% 2.90/0.79    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 2.90/0.79  fof(f45,plain,(
% 2.90/0.79    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.90/0.79    inference(cnf_transformation,[],[f15])).
% 2.90/0.79  fof(f1779,plain,(
% 2.90/0.79    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | (~spl5_2 | ~spl5_44)),
% 2.90/0.79    inference(superposition,[],[f618,f652])).
% 2.90/0.79  fof(f652,plain,(
% 2.90/0.79    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_44),
% 2.90/0.79    inference(avatar_component_clause,[],[f650])).
% 2.90/0.79  fof(f618,plain,(
% 2.90/0.79    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0))) ) | ~spl5_2),
% 2.90/0.79    inference(superposition,[],[f608,f270])).
% 2.90/0.79  fof(f270,plain,(
% 2.90/0.79    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl5_2),
% 2.90/0.79    inference(resolution,[],[f82,f96])).
% 2.90/0.79  fof(f96,plain,(
% 2.90/0.79    v1_relat_1(sK0) | ~spl5_2),
% 2.90/0.79    inference(avatar_component_clause,[],[f94])).
% 2.90/0.79  fof(f82,plain,(
% 2.90/0.79    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 2.90/0.79    inference(definition_unfolding,[],[f68,f80])).
% 2.90/0.79  fof(f80,plain,(
% 2.90/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.90/0.79    inference(definition_unfolding,[],[f55,f79])).
% 2.90/0.79  fof(f79,plain,(
% 2.90/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.90/0.79    inference(definition_unfolding,[],[f56,f78])).
% 2.90/0.79  fof(f78,plain,(
% 2.90/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.90/0.79    inference(definition_unfolding,[],[f67,f77])).
% 2.90/0.79  fof(f77,plain,(
% 2.90/0.79    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.90/0.79    inference(definition_unfolding,[],[f71,f76])).
% 2.90/0.79  fof(f76,plain,(
% 2.90/0.79    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.90/0.79    inference(definition_unfolding,[],[f72,f75])).
% 2.90/0.79  fof(f75,plain,(
% 2.90/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.90/0.79    inference(definition_unfolding,[],[f73,f74])).
% 2.90/0.79  fof(f74,plain,(
% 2.90/0.79    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f10])).
% 2.90/0.79  fof(f10,axiom,(
% 2.90/0.79    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.90/0.79  fof(f73,plain,(
% 2.90/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f9])).
% 2.90/0.79  fof(f9,axiom,(
% 2.90/0.79    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.90/0.79  fof(f72,plain,(
% 2.90/0.79    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f8])).
% 2.90/0.79  fof(f8,axiom,(
% 2.90/0.79    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.90/0.79  fof(f71,plain,(
% 2.90/0.79    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f7])).
% 2.90/0.79  fof(f7,axiom,(
% 2.90/0.79    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.90/0.79  fof(f67,plain,(
% 2.90/0.79    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f6])).
% 2.90/0.79  fof(f6,axiom,(
% 2.90/0.79    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.90/0.79  fof(f56,plain,(
% 2.90/0.79    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f5])).
% 2.90/0.79  fof(f5,axiom,(
% 2.90/0.79    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.90/0.79  fof(f55,plain,(
% 2.90/0.79    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f11])).
% 2.90/0.79  fof(f11,axiom,(
% 2.90/0.79    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.90/0.79  fof(f68,plain,(
% 2.90/0.79    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.90/0.79    inference(cnf_transformation,[],[f36])).
% 2.90/0.79  fof(f36,plain,(
% 2.90/0.79    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.90/0.79    inference(ennf_transformation,[],[f16])).
% 2.90/0.79  fof(f16,axiom,(
% 2.90/0.79    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.90/0.79  fof(f608,plain,(
% 2.90/0.79    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) )),
% 2.90/0.79    inference(forward_demodulation,[],[f320,f426])).
% 2.90/0.79  fof(f320,plain,(
% 2.90/0.79    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1)))) )),
% 2.90/0.79    inference(global_subsumption,[],[f44,f319])).
% 2.90/0.79  fof(f319,plain,(
% 2.90/0.79    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.90/0.79    inference(forward_demodulation,[],[f314,f46])).
% 2.90/0.79  fof(f314,plain,(
% 2.90/0.79    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))))) )),
% 2.90/0.79    inference(resolution,[],[f81,f45])).
% 2.90/0.79  fof(f81,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 2.90/0.79    inference(definition_unfolding,[],[f59,f80])).
% 2.90/0.79  fof(f59,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 2.90/0.79    inference(cnf_transformation,[],[f32])).
% 2.90/0.79  fof(f32,plain,(
% 2.90/0.79    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.90/0.79    inference(flattening,[],[f31])).
% 2.90/0.79  fof(f31,plain,(
% 2.90/0.79    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.90/0.79    inference(ennf_transformation,[],[f19])).
% 2.90/0.79  fof(f19,axiom,(
% 2.90/0.79    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 2.90/0.79  fof(f1007,plain,(
% 2.90/0.79    spl5_45),
% 2.90/0.79    inference(avatar_contradiction_clause,[],[f994])).
% 2.90/0.79  fof(f994,plain,(
% 2.90/0.79    $false | spl5_45),
% 2.90/0.79    inference(resolution,[],[f993,f656])).
% 2.90/0.79  fof(f656,plain,(
% 2.90/0.79    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | spl5_45),
% 2.90/0.79    inference(avatar_component_clause,[],[f654])).
% 2.90/0.79  fof(f654,plain,(
% 2.90/0.79    spl5_45 <=> r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))),
% 2.90/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.90/0.79  fof(f993,plain,(
% 2.90/0.79    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.90/0.79    inference(duplicate_literal_removal,[],[f986])).
% 2.90/0.79  fof(f986,plain,(
% 2.90/0.79    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.90/0.79    inference(resolution,[],[f475,f66])).
% 2.90/0.79  fof(f66,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f35])).
% 2.90/0.79  fof(f35,plain,(
% 2.90/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.90/0.79    inference(ennf_transformation,[],[f1])).
% 2.90/0.79  fof(f1,axiom,(
% 2.90/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.90/0.79  fof(f475,plain,(
% 2.90/0.79    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.90/0.79    inference(global_subsumption,[],[f44,f474])).
% 2.90/0.79  fof(f474,plain,(
% 2.90/0.79    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.90/0.79    inference(forward_demodulation,[],[f469,f46])).
% 2.90/0.79  fof(f469,plain,(
% 2.90/0.79    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.90/0.79    inference(resolution,[],[f185,f45])).
% 2.90/0.79  fof(f185,plain,(
% 2.90/0.79    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),X2)) )),
% 2.90/0.79    inference(resolution,[],[f85,f65])).
% 2.90/0.79  fof(f65,plain,(
% 2.90/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.90/0.79    inference(cnf_transformation,[],[f35])).
% 2.90/0.79  fof(f85,plain,(
% 2.90/0.79    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.90/0.79    inference(equality_resolution,[],[f52])).
% 2.90/0.79  fof(f52,plain,(
% 2.90/0.79    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.90/0.79    inference(cnf_transformation,[],[f27])).
% 2.90/0.79  fof(f27,plain,(
% 2.90/0.79    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.79    inference(flattening,[],[f26])).
% 2.90/0.79  fof(f26,plain,(
% 2.90/0.79    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.79    inference(ennf_transformation,[],[f14])).
% 2.90/0.79  fof(f14,axiom,(
% 2.90/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 2.90/0.79  fof(f657,plain,(
% 2.90/0.79    spl5_44 | ~spl5_45 | ~spl5_19),
% 2.90/0.79    inference(avatar_split_clause,[],[f632,f266,f654,f650])).
% 2.90/0.79  fof(f266,plain,(
% 2.90/0.79    spl5_19 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 2.90/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.90/0.79  fof(f632,plain,(
% 2.90/0.79    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_19),
% 2.90/0.79    inference(resolution,[],[f268,f63])).
% 2.90/0.79  fof(f63,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.90/0.79    inference(cnf_transformation,[],[f2])).
% 2.90/0.79  fof(f268,plain,(
% 2.90/0.79    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl5_19),
% 2.90/0.79    inference(avatar_component_clause,[],[f266])).
% 2.90/0.79  fof(f489,plain,(
% 2.90/0.79    spl5_19 | ~spl5_4),
% 2.90/0.79    inference(avatar_split_clause,[],[f481,f104,f266])).
% 2.90/0.79  fof(f104,plain,(
% 2.90/0.79    spl5_4 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.90/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.90/0.79  fof(f481,plain,(
% 2.90/0.79    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl5_4),
% 2.90/0.79    inference(resolution,[],[f447,f106])).
% 2.90/0.79  fof(f106,plain,(
% 2.90/0.79    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl5_4),
% 2.90/0.79    inference(avatar_component_clause,[],[f104])).
% 2.90/0.79  fof(f447,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.90/0.79    inference(global_subsumption,[],[f44,f45,f86,f446])).
% 2.90/0.79  fof(f446,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.90/0.79    inference(forward_demodulation,[],[f445,f46])).
% 2.90/0.79  fof(f445,plain,(
% 2.90/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_funct_1(k6_relat_1(X0)) | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.90/0.79    inference(superposition,[],[f70,f426])).
% 2.90/0.79  fof(f70,plain,(
% 2.90/0.79    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 2.90/0.79    inference(cnf_transformation,[],[f39])).
% 2.90/0.79  fof(f39,plain,(
% 2.90/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.90/0.79    inference(flattening,[],[f38])).
% 2.90/0.79  fof(f38,plain,(
% 2.90/0.79    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.90/0.79    inference(ennf_transformation,[],[f20])).
% 2.90/0.79  fof(f20,axiom,(
% 2.90/0.79    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 2.90/0.79  fof(f107,plain,(
% 2.90/0.79    spl5_4),
% 2.90/0.79    inference(avatar_split_clause,[],[f40,f104])).
% 2.90/0.79  fof(f40,plain,(
% 2.90/0.79    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.90/0.79    inference(cnf_transformation,[],[f24])).
% 2.90/0.79  fof(f24,plain,(
% 2.90/0.79    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.90/0.79    inference(flattening,[],[f23])).
% 2.90/0.79  fof(f23,plain,(
% 2.90/0.79    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.90/0.79    inference(ennf_transformation,[],[f22])).
% 2.90/0.79  fof(f22,negated_conjecture,(
% 2.90/0.79    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.90/0.79    inference(negated_conjecture,[],[f21])).
% 2.90/0.79  fof(f21,conjecture,(
% 2.90/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.90/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 2.90/0.79  fof(f102,plain,(
% 2.90/0.79    ~spl5_3),
% 2.90/0.79    inference(avatar_split_clause,[],[f41,f99])).
% 2.90/0.79  fof(f41,plain,(
% 2.90/0.79    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.90/0.79    inference(cnf_transformation,[],[f24])).
% 2.90/0.79  fof(f97,plain,(
% 2.90/0.79    spl5_2),
% 2.90/0.79    inference(avatar_split_clause,[],[f42,f94])).
% 2.90/0.79  fof(f42,plain,(
% 2.90/0.79    v1_relat_1(sK0)),
% 2.90/0.79    inference(cnf_transformation,[],[f24])).
% 2.90/0.79  % SZS output end Proof for theBenchmark
% 2.90/0.79  % (13504)------------------------------
% 2.90/0.79  % (13504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.79  % (13504)Termination reason: Refutation
% 2.90/0.79  
% 2.90/0.79  % (13504)Memory used [KB]: 12409
% 2.90/0.79  % (13504)Time elapsed: 0.354 s
% 2.90/0.79  % (13504)------------------------------
% 2.90/0.79  % (13504)------------------------------
% 2.90/0.79  % (13487)Success in time 0.426 s
%------------------------------------------------------------------------------
