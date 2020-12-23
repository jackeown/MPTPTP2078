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
% DateTime   : Thu Dec  3 12:55:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 214 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  217 ( 422 expanded)
%              Number of equality atoms :   51 ( 134 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f119,f215,f256,f260,f341,f426])).

fof(f426,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl3_12
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f34,f209,f206,f278])).

fof(f278,plain,(
    ! [X4] :
      ( r1_tarski(k2_relat_1(k2_wellord1(X4,sK0)),sK1)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k2_wellord1(X4,sK0)) ) ),
    inference(resolution,[],[f272,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X0,sK0)))
      | ~ v1_relat_1(X0)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X0,sK0)),sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f272,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f241,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X0))
      | r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f64,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f206,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_12
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f209,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_13
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f341,plain,
    ( ~ spl3_13
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl3_13
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f34,f209,f255,f314])).

fof(f314,plain,(
    ! [X17] :
      ( r1_tarski(k1_relat_1(k2_wellord1(X17,sK0)),sK1)
      | ~ v1_relat_1(X17)
      | ~ v1_relat_1(k2_wellord1(X17,sK0)) ) ),
    inference(resolution,[],[f244,f80])).

fof(f244,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(k2_wellord1(X2,X3)),X3)
      | ~ v1_relat_1(k2_wellord1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f242,f82])).

fof(f82,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k3_relat_1(k2_wellord1(X4,X5)))
      | r1_tarski(X3,X5)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f53,f44])).

fof(f242,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f63,f62])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f255,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl3_20
  <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f260,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f34,f210,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f210,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f256,plain,
    ( ~ spl3_13
    | ~ spl3_20
    | spl3_14 ),
    inference(avatar_split_clause,[],[f250,f212,f253,f208])).

fof(f212,plain,
    ( spl3_14
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f250,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(superposition,[],[f214,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f214,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f212])).

fof(f215,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | spl3_4 ),
    inference(avatar_split_clause,[],[f161,f113,f212,f208,f204])).

fof(f113,plain,
    ( spl3_4
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f161,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_4 ),
    inference(superposition,[],[f115,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f115,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f119,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f34,f111])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f117,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f103,f113,f109])).

fof(f103,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f36,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:59:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (31018)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (31026)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (31019)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31014)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (31024)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (31043)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (31017)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (31015)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (31029)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (31027)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (31016)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (31032)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (31030)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (31031)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (31044)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (31021)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (31041)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (31025)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (31022)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (31033)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (31035)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (31023)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (31034)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (31040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (31038)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (31042)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (31039)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (31027)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f427,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f117,f119,f215,f256,f260,f341,f426])).
% 0.21/0.56  fof(f426,plain,(
% 0.21/0.56    spl3_12 | ~spl3_13),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f416])).
% 0.21/0.56  fof(f416,plain,(
% 0.21/0.56    $false | (spl3_12 | ~spl3_13)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f34,f209,f206,f278])).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    ( ! [X4] : (r1_tarski(k2_relat_1(k2_wellord1(X4,sK0)),sK1) | ~v1_relat_1(X4) | ~v1_relat_1(k2_wellord1(X4,sK0))) )),
% 0.21/0.56    inference(resolution,[],[f272,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,k3_relat_1(k2_wellord1(X0,sK0))) | ~v1_relat_1(X0) | r1_tarski(X1,sK1)) )),
% 0.21/0.56    inference(resolution,[],[f85,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(X0,sK0)),sK1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f80,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f53,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    r1_tarski(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.57    inference(negated_conjecture,[],[f18])).
% 0.21/0.57  fof(f18,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f241,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f241,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(X0)) | r1_tarski(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(superposition,[],[f64,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f37,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f39,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f40,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f50,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f55,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f52,f61])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.57  fof(f206,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f204])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    spl3_12 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.57  fof(f209,plain,(
% 0.21/0.57    v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl3_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f208])).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    spl3_13 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f341,plain,(
% 0.21/0.57    ~spl3_13 | spl3_20),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f333])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    $false | (~spl3_13 | spl3_20)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f34,f209,f255,f314])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    ( ! [X17] : (r1_tarski(k1_relat_1(k2_wellord1(X17,sK0)),sK1) | ~v1_relat_1(X17) | ~v1_relat_1(k2_wellord1(X17,sK0))) )),
% 0.21/0.57    inference(resolution,[],[f244,f80])).
% 0.21/0.57  fof(f244,plain,(
% 0.21/0.57    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k2_wellord1(X2,X3)),X3) | ~v1_relat_1(k2_wellord1(X2,X3)) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(resolution,[],[f242,f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X3,k3_relat_1(k2_wellord1(X4,X5))) | r1_tarski(X3,X5) | ~v1_relat_1(X4)) )),
% 0.21/0.57    inference(resolution,[],[f53,f44])).
% 0.21/0.57  fof(f242,plain,(
% 0.21/0.57    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(superposition,[],[f63,f62])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f38,f61])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f253])).
% 0.21/0.57  fof(f253,plain,(
% 0.21/0.57    spl3_20 <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.57  fof(f260,plain,(
% 0.21/0.57    spl3_13),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    $false | spl3_13),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f34,f210,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f208])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ~spl3_13 | ~spl3_20 | spl3_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f250,f212,f253,f208])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    spl3_14 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.57  fof(f250,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_14),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f249])).
% 0.21/0.57  fof(f249,plain,(
% 0.21/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_14),
% 0.21/0.57    inference(superposition,[],[f214,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.57  fof(f214,plain,(
% 0.21/0.57    k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f212])).
% 0.21/0.57  fof(f215,plain,(
% 0.21/0.57    ~spl3_12 | ~spl3_13 | ~spl3_14 | spl3_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f161,f113,f212,f208,f204])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    spl3_4 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_4),
% 0.21/0.57    inference(superposition,[],[f115,f89])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(superposition,[],[f42,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | spl3_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f113])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    spl3_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    $false | spl3_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f34,f111])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl3_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f109])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ~spl3_3 | ~spl3_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f103,f113,f109])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 0.21/0.57    inference(superposition,[],[f36,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (31027)------------------------------
% 0.21/0.57  % (31027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (31027)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (31027)Memory used [KB]: 6524
% 0.21/0.57  % (31027)Time elapsed: 0.167 s
% 0.21/0.57  % (31027)------------------------------
% 0.21/0.57  % (31027)------------------------------
% 0.21/0.57  % (31013)Success in time 0.205 s
%------------------------------------------------------------------------------
