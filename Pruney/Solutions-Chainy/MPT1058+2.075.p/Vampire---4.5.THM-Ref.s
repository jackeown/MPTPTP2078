%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:27 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 440 expanded)
%              Number of leaves         :   24 ( 146 expanded)
%              Depth                    :   21
%              Number of atoms          :  228 ( 756 expanded)
%              Number of equality atoms :   80 ( 350 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f88,f93,f112,f218,f4827,f5353])).

fof(f5353,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f5352])).

fof(f5352,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f5351,f92])).

fof(f92,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_4
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f5351,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f5341,f135])).

fof(f135,plain,
    ( ! [X0] : k10_relat_1(sK0,X0) = k1_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f101,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f101,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f77,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f5341,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k1_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,sK2)))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(superposition,[],[f446,f4826])).

fof(f4826,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f4824])).

fof(f4824,plain,
    ( spl3_16
  <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f446,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X0),X1)))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f445,f435])).

fof(f435,plain,
    ( ! [X0,X1] : k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,X0),X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f222,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f222,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X0)
    | ~ spl3_1 ),
    inference(superposition,[],[f70,f138])).

fof(f138,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f445,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,X0),X1)))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f424,f260])).

fof(f260,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f256,f111])).

fof(f111,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_5
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f256,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f152,f154])).

fof(f154,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f153,f111])).

fof(f153,plain,
    ( ! [X0] : k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0)) = k1_relat_1(k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f113,f152])).

fof(f113,plain,
    ( ! [X0] : k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0)) = k1_relat_1(k7_relat_1(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0))))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f70,f55])).

fof(f152,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f150,f103])).

fof(f103,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(f150,plain,
    ( ! [X0,X1] : k7_relat_1(sK0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X0),X1)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f125,f144])).

fof(f144,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1),X2) = k7_relat_1(k7_relat_1(sK0,X0),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f94,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f125,plain,
    ( ! [X0,X1] : k7_relat_1(sK0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK0,X0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f70,f61])).

fof(f424,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))),X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f222,f116])).

fof(f116,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3))) ) ),
    inference(resolution,[],[f55,f52])).

fof(f4827,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f654,f215,f75,f4824])).

fof(f215,plain,
    ( spl3_7
  <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f654,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f246,f217])).

fof(f217,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f215])).

fof(f246,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X0),X1))
    | ~ spl3_1 ),
    inference(superposition,[],[f152,f138])).

fof(f218,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f123,f85,f75,f215])).

fof(f85,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f123,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f77,f87,f61])).

fof(f87,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f112,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f96,f75,f109])).

fof(f96,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f77,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f93,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

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

fof(f88,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f85])).

fof(f43,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11364)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (11362)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (11367)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (11371)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (11365)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (11363)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (11372)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (11369)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (11373)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (11379)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (11377)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (11370)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (11376)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (11366)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (11368)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (11375)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (11378)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (11374)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 3.77/0.85  % (11377)Refutation found. Thanks to Tanya!
% 3.77/0.85  % SZS status Theorem for theBenchmark
% 4.00/0.87  % SZS output start Proof for theBenchmark
% 4.00/0.87  fof(f5356,plain,(
% 4.00/0.87    $false),
% 4.00/0.87    inference(avatar_sat_refutation,[],[f78,f88,f93,f112,f218,f4827,f5353])).
% 4.00/0.87  fof(f5353,plain,(
% 4.00/0.87    ~spl3_1 | spl3_4 | ~spl3_5 | ~spl3_16),
% 4.00/0.87    inference(avatar_contradiction_clause,[],[f5352])).
% 4.00/0.87  fof(f5352,plain,(
% 4.00/0.87    $false | (~spl3_1 | spl3_4 | ~spl3_5 | ~spl3_16)),
% 4.00/0.87    inference(subsumption_resolution,[],[f5351,f92])).
% 4.00/0.87  fof(f92,plain,(
% 4.00/0.87    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_4),
% 4.00/0.87    inference(avatar_component_clause,[],[f90])).
% 4.00/0.87  fof(f90,plain,(
% 4.00/0.87    spl3_4 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.00/0.87  fof(f5351,plain,(
% 4.00/0.87    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_1 | ~spl3_5 | ~spl3_16)),
% 4.00/0.87    inference(forward_demodulation,[],[f5341,f135])).
% 4.00/0.87  fof(f135,plain,(
% 4.00/0.87    ( ! [X0] : (k10_relat_1(sK0,X0) = k1_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f101,f55])).
% 4.00/0.87  fof(f55,plain,(
% 4.00/0.87    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 4.00/0.87    inference(cnf_transformation,[],[f30])).
% 4.00/0.87  fof(f30,plain,(
% 4.00/0.87    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.00/0.87    inference(flattening,[],[f29])).
% 4.00/0.87  fof(f29,plain,(
% 4.00/0.87    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.00/0.87    inference(ennf_transformation,[],[f18])).
% 4.00/0.87  fof(f18,axiom,(
% 4.00/0.87    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 4.00/0.87  fof(f101,plain,(
% 4.00/0.87    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f53])).
% 4.00/0.87  fof(f53,plain,(
% 4.00/0.87    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f27])).
% 4.00/0.87  fof(f27,plain,(
% 4.00/0.87    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.00/0.87    inference(ennf_transformation,[],[f16])).
% 4.00/0.87  fof(f16,axiom,(
% 4.00/0.87    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 4.00/0.87  fof(f77,plain,(
% 4.00/0.87    v1_relat_1(sK0) | ~spl3_1),
% 4.00/0.87    inference(avatar_component_clause,[],[f75])).
% 4.00/0.87  fof(f75,plain,(
% 4.00/0.87    spl3_1 <=> v1_relat_1(sK0)),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.00/0.87  fof(f5341,plain,(
% 4.00/0.87    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k1_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,sK2))) | (~spl3_1 | ~spl3_5 | ~spl3_16)),
% 4.00/0.87    inference(superposition,[],[f446,f4826])).
% 4.00/0.87  fof(f4826,plain,(
% 4.00/0.87    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | ~spl3_16),
% 4.00/0.87    inference(avatar_component_clause,[],[f4824])).
% 4.00/0.87  fof(f4824,plain,(
% 4.00/0.87    spl3_16 <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2))),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 4.00/0.87  fof(f446,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X0),X1)))) ) | (~spl3_1 | ~spl3_5)),
% 4.00/0.87    inference(forward_demodulation,[],[f445,f435])).
% 4.00/0.87  fof(f435,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,X0),X1))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f222,f61])).
% 4.00/0.87  fof(f61,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f37])).
% 4.00/0.87  fof(f37,plain,(
% 4.00/0.87    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 4.00/0.87    inference(flattening,[],[f36])).
% 4.00/0.87  fof(f36,plain,(
% 4.00/0.87    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 4.00/0.87    inference(ennf_transformation,[],[f14])).
% 4.00/0.87  fof(f14,axiom,(
% 4.00/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 4.00/0.87  fof(f222,plain,(
% 4.00/0.87    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X0)) ) | ~spl3_1),
% 4.00/0.87    inference(superposition,[],[f70,f138])).
% 4.00/0.87  fof(f138,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f71])).
% 4.00/0.87  fof(f71,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 4.00/0.87    inference(definition_unfolding,[],[f57,f69])).
% 4.00/0.87  fof(f69,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 4.00/0.87    inference(definition_unfolding,[],[f50,f68])).
% 4.00/0.87  fof(f68,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 4.00/0.87    inference(definition_unfolding,[],[f51,f67])).
% 4.00/0.87  fof(f67,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 4.00/0.87    inference(definition_unfolding,[],[f56,f66])).
% 4.00/0.87  fof(f66,plain,(
% 4.00/0.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 4.00/0.87    inference(definition_unfolding,[],[f62,f65])).
% 4.00/0.87  fof(f65,plain,(
% 4.00/0.87    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 4.00/0.87    inference(definition_unfolding,[],[f63,f64])).
% 4.00/0.87  fof(f64,plain,(
% 4.00/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f8])).
% 4.00/0.87  fof(f8,axiom,(
% 4.00/0.87    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 4.00/0.87  fof(f63,plain,(
% 4.00/0.87    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f7])).
% 4.00/0.87  fof(f7,axiom,(
% 4.00/0.87    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.00/0.87  fof(f62,plain,(
% 4.00/0.87    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f6])).
% 4.00/0.87  fof(f6,axiom,(
% 4.00/0.87    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.00/0.87  fof(f56,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f5])).
% 4.00/0.87  fof(f5,axiom,(
% 4.00/0.87    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.00/0.87  fof(f51,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f4])).
% 4.00/0.87  fof(f4,axiom,(
% 4.00/0.87    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.00/0.87  fof(f50,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.00/0.87    inference(cnf_transformation,[],[f10])).
% 4.00/0.87  fof(f10,axiom,(
% 4.00/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.00/0.87  fof(f57,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f31])).
% 4.00/0.87  fof(f31,plain,(
% 4.00/0.87    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.00/0.87    inference(ennf_transformation,[],[f20])).
% 4.00/0.87  fof(f20,axiom,(
% 4.00/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 4.00/0.87  fof(f70,plain,(
% 4.00/0.87    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 4.00/0.87    inference(definition_unfolding,[],[f48,f69])).
% 4.00/0.87  fof(f48,plain,(
% 4.00/0.87    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f1])).
% 4.00/0.87  fof(f1,axiom,(
% 4.00/0.87    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.00/0.87  fof(f445,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,X0),X1)))) ) | (~spl3_1 | ~spl3_5)),
% 4.00/0.87    inference(forward_demodulation,[],[f424,f260])).
% 4.00/0.87  fof(f260,plain,(
% 4.00/0.87    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl3_1 | ~spl3_5)),
% 4.00/0.87    inference(forward_demodulation,[],[f256,f111])).
% 4.00/0.87  fof(f111,plain,(
% 4.00/0.87    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl3_5),
% 4.00/0.87    inference(avatar_component_clause,[],[f109])).
% 4.00/0.87  fof(f109,plain,(
% 4.00/0.87    spl3_5 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.00/0.87  fof(f256,plain,(
% 4.00/0.87    ( ! [X0] : (k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl3_1 | ~spl3_5)),
% 4.00/0.87    inference(superposition,[],[f152,f154])).
% 4.00/0.87  fof(f154,plain,(
% 4.00/0.87    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0))) ) | (~spl3_1 | ~spl3_5)),
% 4.00/0.87    inference(forward_demodulation,[],[f153,f111])).
% 4.00/0.87  fof(f153,plain,(
% 4.00/0.87    ( ! [X0] : (k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0)) = k1_relat_1(k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0))) ) | ~spl3_1),
% 4.00/0.87    inference(backward_demodulation,[],[f113,f152])).
% 4.00/0.87  fof(f113,plain,(
% 4.00/0.87    ( ! [X0] : (k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0)) = k1_relat_1(k7_relat_1(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),X0))))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f70,f55])).
% 4.00/0.87  fof(f152,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl3_1),
% 4.00/0.87    inference(forward_demodulation,[],[f150,f103])).
% 4.00/0.87  fof(f103,plain,(
% 4.00/0.87    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0)) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f54])).
% 4.00/0.87  fof(f54,plain,(
% 4.00/0.87    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f28])).
% 4.00/0.87  fof(f28,plain,(
% 4.00/0.87    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 4.00/0.87    inference(ennf_transformation,[],[f13])).
% 4.00/0.87  fof(f13,axiom,(
% 4.00/0.87    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).
% 4.00/0.87  fof(f150,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k7_relat_1(sK0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X0),X1)) ) | ~spl3_1),
% 4.00/0.87    inference(backward_demodulation,[],[f125,f144])).
% 4.00/0.87  fof(f144,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1),X2) = k7_relat_1(k7_relat_1(sK0,X0),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f94,f72])).
% 4.00/0.87  fof(f72,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.00/0.87    inference(definition_unfolding,[],[f58,f69])).
% 4.00/0.87  fof(f58,plain,(
% 4.00/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f32])).
% 4.00/0.87  fof(f32,plain,(
% 4.00/0.87    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 4.00/0.87    inference(ennf_transformation,[],[f12])).
% 4.00/0.87  fof(f12,axiom,(
% 4.00/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 4.00/0.87  fof(f94,plain,(
% 4.00/0.87    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f52])).
% 4.00/0.87  fof(f52,plain,(
% 4.00/0.87    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.00/0.87    inference(cnf_transformation,[],[f26])).
% 4.00/0.87  fof(f26,plain,(
% 4.00/0.87    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.00/0.87    inference(ennf_transformation,[],[f11])).
% 4.00/0.87  fof(f11,axiom,(
% 4.00/0.87    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.00/0.87  fof(f125,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k7_relat_1(sK0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK0,X0),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f70,f61])).
% 4.00/0.87  fof(f424,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))),X1)))) ) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f222,f116])).
% 4.00/0.87  fof(f116,plain,(
% 4.00/0.87    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))) )),
% 4.00/0.87    inference(resolution,[],[f55,f52])).
% 4.00/0.87  fof(f4827,plain,(
% 4.00/0.87    spl3_16 | ~spl3_1 | ~spl3_7),
% 4.00/0.87    inference(avatar_split_clause,[],[f654,f215,f75,f4824])).
% 4.00/0.87  fof(f215,plain,(
% 4.00/0.87    spl3_7 <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 4.00/0.87  fof(f654,plain,(
% 4.00/0.87    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | (~spl3_1 | ~spl3_7)),
% 4.00/0.87    inference(superposition,[],[f246,f217])).
% 4.00/0.87  fof(f217,plain,(
% 4.00/0.87    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | ~spl3_7),
% 4.00/0.87    inference(avatar_component_clause,[],[f215])).
% 4.00/0.87  fof(f246,plain,(
% 4.00/0.87    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X0),X1))) ) | ~spl3_1),
% 4.00/0.87    inference(superposition,[],[f152,f138])).
% 4.00/0.87  fof(f218,plain,(
% 4.00/0.87    spl3_7 | ~spl3_1 | ~spl3_3),
% 4.00/0.87    inference(avatar_split_clause,[],[f123,f85,f75,f215])).
% 4.00/0.87  fof(f85,plain,(
% 4.00/0.87    spl3_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 4.00/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.00/0.87  fof(f123,plain,(
% 4.00/0.87    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | (~spl3_1 | ~spl3_3)),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f87,f61])).
% 4.00/0.87  fof(f87,plain,(
% 4.00/0.87    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_3),
% 4.00/0.87    inference(avatar_component_clause,[],[f85])).
% 4.00/0.87  fof(f112,plain,(
% 4.00/0.87    spl3_5 | ~spl3_1),
% 4.00/0.87    inference(avatar_split_clause,[],[f96,f75,f109])).
% 4.00/0.87  fof(f96,plain,(
% 4.00/0.87    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl3_1),
% 4.00/0.87    inference(unit_resulting_resolution,[],[f77,f47])).
% 4.00/0.87  fof(f47,plain,(
% 4.00/0.87    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 4.00/0.87    inference(cnf_transformation,[],[f25])).
% 4.00/0.87  fof(f25,plain,(
% 4.00/0.87    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.00/0.87    inference(ennf_transformation,[],[f19])).
% 4.00/0.87  fof(f19,axiom,(
% 4.00/0.87    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 4.00/0.87  fof(f93,plain,(
% 4.00/0.87    ~spl3_4),
% 4.00/0.87    inference(avatar_split_clause,[],[f44,f90])).
% 4.00/0.87  fof(f44,plain,(
% 4.00/0.87    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 4.00/0.87    inference(cnf_transformation,[],[f40])).
% 4.00/0.87  fof(f40,plain,(
% 4.00/0.87    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 4.00/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f39,f38])).
% 4.00/0.87  fof(f38,plain,(
% 4.00/0.87    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 4.00/0.87    introduced(choice_axiom,[])).
% 4.00/0.87  fof(f39,plain,(
% 4.00/0.87    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 4.00/0.87    introduced(choice_axiom,[])).
% 4.00/0.87  fof(f24,plain,(
% 4.00/0.87    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 4.00/0.87    inference(flattening,[],[f23])).
% 4.00/0.87  fof(f23,plain,(
% 4.00/0.87    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 4.00/0.87    inference(ennf_transformation,[],[f22])).
% 4.00/0.87  fof(f22,negated_conjecture,(
% 4.00/0.87    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 4.00/0.87    inference(negated_conjecture,[],[f21])).
% 4.00/0.87  fof(f21,conjecture,(
% 4.00/0.87    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 4.00/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 4.00/0.87  fof(f88,plain,(
% 4.00/0.87    spl3_3),
% 4.00/0.87    inference(avatar_split_clause,[],[f43,f85])).
% 4.00/0.87  fof(f43,plain,(
% 4.00/0.87    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 4.00/0.87    inference(cnf_transformation,[],[f40])).
% 4.00/0.87  fof(f78,plain,(
% 4.00/0.87    spl3_1),
% 4.00/0.87    inference(avatar_split_clause,[],[f41,f75])).
% 4.00/0.87  fof(f41,plain,(
% 4.00/0.87    v1_relat_1(sK0)),
% 4.00/0.87    inference(cnf_transformation,[],[f40])).
% 4.00/0.87  % SZS output end Proof for theBenchmark
% 4.00/0.87  % (11377)------------------------------
% 4.00/0.87  % (11377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.87  % (11377)Termination reason: Refutation
% 4.00/0.87  
% 4.00/0.87  % (11377)Memory used [KB]: 18038
% 4.00/0.87  % (11377)Time elapsed: 0.446 s
% 4.00/0.87  % (11377)------------------------------
% 4.00/0.87  % (11377)------------------------------
% 4.00/0.87  % (11358)Success in time 0.511 s
%------------------------------------------------------------------------------
