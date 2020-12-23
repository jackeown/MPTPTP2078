%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 183 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 ( 382 expanded)
%              Number of equality atoms :   86 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f668,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f66,f70,f74,f78,f85,f96,f108,f116,f120,f126,f137,f165,f500,f667])).

fof(f667,plain,
    ( spl3_12
    | ~ spl3_18
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | spl3_12
    | ~ spl3_18
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f665,f136])).

fof(f136,plain,
    ( ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2)) = k9_relat_1(k8_relat_1(X1,sK2),X2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_18
  <=> ! [X1,X2] : k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2)) = k9_relat_1(k8_relat_1(X1,sK2),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f665,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k9_relat_1(k6_relat_1(sK0),k9_relat_1(sK2,sK1))
    | spl3_12
    | ~ spl3_45 ),
    inference(superposition,[],[f107,f499])).

fof(f499,plain,
    ( ! [X4,X5] : k9_relat_1(k6_relat_1(X4),X5) = k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl3_45
  <=> ! [X5,X4] : k9_relat_1(k6_relat_1(X4),X5) = k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f107,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_12
  <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f500,plain,
    ( spl3_45
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f208,f163,f114,f64,f498])).

fof(f64,plain,
    ( spl3_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f114,plain,
    ( spl3_14
  <=> ! [X1,X2] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f163,plain,
    ( spl3_23
  <=> ! [X1,X0] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f208,plain,
    ( ! [X4,X5] : k9_relat_1(k6_relat_1(X4),X5) = k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f193,f115])).

fof(f115,plain,
    ( ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f193,plain,
    ( ! [X4,X5] : k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)) = k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(superposition,[],[f65,f164])).

fof(f164,plain,
    ( ! [X0,X1] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f65,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f165,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f81,f68,f56,f163])).

fof(f56,plain,
    ( spl3_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( ! [X0,X1] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f49,f80])).

fof(f80,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f49,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f137,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f129,f124,f83,f56,f135])).

fof(f83,plain,
    ( spl3_8
  <=> ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f124,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(sK2,X0),X1) = k9_relat_1(X0,k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f129,plain,
    ( ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2)) = k9_relat_1(k8_relat_1(X1,sK2),X2)
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f128,f84])).

fof(f84,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f128,plain,
    ( ! [X2,X1] : k9_relat_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2))
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(resolution,[],[f125,f57])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(sK2,X0),X1) = k9_relat_1(X0,k9_relat_1(sK2,X1)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f121,f118,f51,f124])).

fof(f51,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f118,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(sK2,X0),X1) = k9_relat_1(X0,k9_relat_1(sK2,X1)) )
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(resolution,[],[f119,f53])).

fof(f53,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f36,f118])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f116,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f94,f76,f56,f114])).

fof(f76,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f94,plain,
    ( spl3_10
  <=> ! [X1,X2] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f98,f95])).

fof(f95,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f98,plain,
    ( ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f77,f57])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f108,plain,(
    ~ spl3_12 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1))) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f26,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f96,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f88,f72,f68,f56,f94])).

fof(f72,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f88,plain,
    ( ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f87,f80])).

fof(f87,plain,
    ( ! [X2,X1] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f73,f57])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f85,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f79,f68,f51,f83])).

fof(f79,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f69,f53])).

fof(f78,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f74,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (7587)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (7581)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (7584)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (7594)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (7587)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f668,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f54,f58,f66,f70,f74,f78,f85,f96,f108,f116,f120,f126,f137,f165,f500,f667])).
% 0.20/0.47  fof(f667,plain,(
% 0.20/0.47    spl3_12 | ~spl3_18 | ~spl3_45),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f666])).
% 0.20/0.47  fof(f666,plain,(
% 0.20/0.47    $false | (spl3_12 | ~spl3_18 | ~spl3_45)),
% 0.20/0.47    inference(subsumption_resolution,[],[f665,f136])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2)) = k9_relat_1(k8_relat_1(X1,sK2),X2)) ) | ~spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl3_18 <=> ! [X1,X2] : k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2)) = k9_relat_1(k8_relat_1(X1,sK2),X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.47  fof(f665,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k9_relat_1(k6_relat_1(sK0),k9_relat_1(sK2,sK1)) | (spl3_12 | ~spl3_45)),
% 0.20/0.47    inference(superposition,[],[f107,f499])).
% 0.20/0.47  fof(f499,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k9_relat_1(k6_relat_1(X4),X5) = k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) ) | ~spl3_45),
% 0.20/0.47    inference(avatar_component_clause,[],[f498])).
% 0.20/0.47  fof(f498,plain,(
% 0.20/0.47    spl3_45 <=> ! [X5,X4] : k9_relat_1(k6_relat_1(X4),X5) = k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1))) | spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl3_12 <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f500,plain,(
% 0.20/0.47    spl3_45 | ~spl3_4 | ~spl3_14 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f208,f163,f114,f64,f498])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl3_14 <=> ! [X1,X2] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl3_23 <=> ! [X1,X0] : k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k9_relat_1(k6_relat_1(X4),X5) = k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) ) | (~spl3_4 | ~spl3_14 | ~spl3_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f193,f115])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) ) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f114])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)) = k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))) ) | (~spl3_4 | ~spl3_23)),
% 0.20/0.47    inference(superposition,[],[f65,f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))) ) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f163])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl3_23 | ~spl3_2 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f81,f68,f56,f163])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl3_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_5 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl3_2 | ~spl3_5)),
% 0.20/0.47    inference(backward_demodulation,[],[f49,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ) | (~spl3_2 | ~spl3_5)),
% 0.20/0.47    inference(resolution,[],[f69,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f32,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f30,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f31,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f37,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f38,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f39,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f40,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    spl3_18 | ~spl3_2 | ~spl3_8 | ~spl3_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f129,f124,f83,f56,f135])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_8 <=> ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_16 <=> ! [X1,X0] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(sK2,X0),X1) = k9_relat_1(X0,k9_relat_1(sK2,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2)) = k9_relat_1(k8_relat_1(X1,sK2),X2)) ) | (~spl3_2 | ~spl3_8 | ~spl3_16)),
% 0.20/0.47    inference(forward_demodulation,[],[f128,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k9_relat_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X2))) ) | (~spl3_2 | ~spl3_16)),
% 0.20/0.47    inference(resolution,[],[f125,f57])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(sK2,X0),X1) = k9_relat_1(X0,k9_relat_1(sK2,X1))) ) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl3_16 | ~spl3_1 | ~spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f121,f118,f51,f124])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl3_15 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(sK2,X0),X1) = k9_relat_1(X0,k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_15)),
% 0.20/0.47    inference(resolution,[],[f119,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f118])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl3_14 | ~spl3_2 | ~spl3_7 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f99,f94,f76,f56,f114])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X2] : k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) ) | (~spl3_2 | ~spl3_7 | ~spl3_10)),
% 0.20/0.47    inference(forward_demodulation,[],[f98,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f94])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) ) | (~spl3_2 | ~spl3_7)),
% 0.20/0.47    inference(resolution,[],[f77,f57])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ~spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f105])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1)))),
% 0.20/0.47    inference(definition_unfolding,[],[f26,f47])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.47  fof(f16,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f15])).
% 0.20/0.47  fof(f15,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl3_10 | ~spl3_2 | ~spl3_5 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f88,f72,f68,f56,f94])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl3_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2)) ) | (~spl3_2 | ~spl3_5 | ~spl3_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f87,f80])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2)) ) | (~spl3_2 | ~spl3_6)),
% 0.20/0.47    inference(resolution,[],[f73,f57])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl3_8 | ~spl3_1 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f79,f68,f51,f83])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | (~spl3_1 | ~spl3_5)),
% 0.20/0.47    inference(resolution,[],[f69,f53])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f76])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f72])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f68])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f56])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f51])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (7587)------------------------------
% 0.20/0.47  % (7587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7587)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (7587)Memory used [KB]: 6908
% 0.20/0.47  % (7587)Time elapsed: 0.030 s
% 0.20/0.47  % (7587)------------------------------
% 0.20/0.47  % (7587)------------------------------
% 0.20/0.47  % (7593)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (7583)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (7576)Success in time 0.119 s
%------------------------------------------------------------------------------
