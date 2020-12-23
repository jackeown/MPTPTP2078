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
% DateTime   : Thu Dec  3 12:35:24 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 253 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 339 expanded)
%              Number of equality atoms :   80 ( 241 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f199,f1099,f1146,f1166,f1172])).

fof(f1172,plain,
    ( spl2_1
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f1169])).

fof(f1169,plain,
    ( $false
    | spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f60,f1165,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f35,f51,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f1165,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1163,plain,
    ( spl2_7
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f60,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1166,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f1152,f1142,f1163])).

fof(f1142,plain,
    ( spl2_6
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1152,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_6 ),
    inference(superposition,[],[f44,f1144])).

fof(f1144,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f1142])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1146,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f1138,f1096,f1142])).

fof(f1096,plain,
    ( spl2_5
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1138,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f1119,f63])).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1119,plain,
    ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f799,f1098])).

fof(f1098,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f1096])).

fof(f799,plain,(
    ! [X31,X32] : k5_xboole_0(k5_xboole_0(X31,X32),X31) = X32 ),
    inference(forward_demodulation,[],[f782,f63])).

fof(f782,plain,(
    ! [X31,X32] : k5_xboole_0(k5_xboole_0(X31,X32),X31) = k5_xboole_0(k1_xboole_0,X32) ),
    inference(superposition,[],[f350,f678])).

fof(f678,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(X7,X8)) = X8 ),
    inference(forward_demodulation,[],[f662,f63])).

fof(f662,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(X7,X8)) = k5_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f37,f651])).

fof(f651,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(global_subsumption,[],[f76,f650])).

fof(f650,plain,(
    ! [X5] :
      ( ~ r1_tarski(k5_xboole_0(X5,X5),X5)
      | k1_xboole_0 = k5_xboole_0(X5,X5) ) ),
    inference(duplicate_literal_removal,[],[f638])).

fof(f638,plain,(
    ! [X5] :
      ( ~ r1_tarski(k5_xboole_0(X5,X5),X5)
      | k1_xboole_0 = k5_xboole_0(X5,X5)
      | ~ r1_tarski(k5_xboole_0(X5,X5),X5) ) ),
    inference(superposition,[],[f115,f104])).

fof(f104,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f53,f47])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k5_xboole_0(X1,X2))
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f55,f82])).

fof(f82,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(X4,X3) = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f56,f47])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f350,plain,(
    ! [X26,X27] : k5_xboole_0(X27,X26) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X26,X27)) ),
    inference(superposition,[],[f144,f63])).

fof(f144,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f37,f39])).

fof(f1099,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f789,f196,f1096])).

fof(f196,plain,
    ( spl2_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f789,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f764,f651])).

fof(f764,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f678,f198])).

fof(f198,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f194,f196])).

fof(f194,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f52,f46])).

fof(f52,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f31,f51,f49,f51,f51])).

fof(f31,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f61,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.43/0.55  % (31332)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.43/0.55  % (31346)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.56  % (31338)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.43/0.56  % (31342)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.56  % (31337)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.57  % (31354)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.57  % (31334)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.62/0.57  % (31343)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.62/0.57  % (31336)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.62/0.57  % (31350)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.62/0.58  % (31331)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.59  % (31355)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.62/0.59  % (31333)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.62/0.59  % (31349)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.62/0.59  % (31335)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.62/0.59  % (31360)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.62/0.59  % (31349)Refutation not found, incomplete strategy% (31349)------------------------------
% 1.62/0.59  % (31349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (31349)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (31349)Memory used [KB]: 1663
% 1.62/0.59  % (31349)Time elapsed: 0.170 s
% 1.62/0.59  % (31349)------------------------------
% 1.62/0.59  % (31349)------------------------------
% 1.62/0.59  % (31343)Refutation not found, incomplete strategy% (31343)------------------------------
% 1.62/0.59  % (31343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (31343)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (31343)Memory used [KB]: 10618
% 1.62/0.59  % (31343)Time elapsed: 0.171 s
% 1.62/0.59  % (31343)------------------------------
% 1.62/0.59  % (31343)------------------------------
% 1.62/0.59  % (31360)Refutation not found, incomplete strategy% (31360)------------------------------
% 1.62/0.59  % (31360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (31360)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (31360)Memory used [KB]: 1663
% 1.62/0.59  % (31360)Time elapsed: 0.002 s
% 1.62/0.59  % (31360)------------------------------
% 1.62/0.59  % (31360)------------------------------
% 1.62/0.60  % (31345)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.62/0.60  % (31359)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.62/0.60  % (31345)Refutation not found, incomplete strategy% (31345)------------------------------
% 1.62/0.60  % (31345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (31345)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (31345)Memory used [KB]: 1663
% 1.62/0.60  % (31345)Time elapsed: 0.181 s
% 1.62/0.60  % (31345)------------------------------
% 1.62/0.60  % (31345)------------------------------
% 1.62/0.60  % (31357)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.60  % (31357)Refutation not found, incomplete strategy% (31357)------------------------------
% 1.62/0.60  % (31357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (31357)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (31357)Memory used [KB]: 6140
% 1.62/0.60  % (31357)Time elapsed: 0.181 s
% 1.62/0.60  % (31357)------------------------------
% 1.62/0.60  % (31357)------------------------------
% 1.62/0.60  % (31353)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.62/0.61  % (31341)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.62/0.61  % (31352)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.62/0.61  % (31351)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.62/0.61  % (31339)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.62/0.61  % (31344)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.62/0.62  % (31358)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.62/0.62  % (31347)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.62  % (31347)Refutation not found, incomplete strategy% (31347)------------------------------
% 1.62/0.62  % (31347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (31347)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.62  
% 1.62/0.62  % (31347)Memory used [KB]: 10618
% 1.62/0.62  % (31347)Time elapsed: 0.198 s
% 1.62/0.62  % (31347)------------------------------
% 1.62/0.62  % (31347)------------------------------
% 1.62/0.63  % (31340)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.62/0.63  % (31348)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.62/0.64  % (31356)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.23/0.66  % (31354)Refutation found. Thanks to Tanya!
% 2.23/0.66  % SZS status Theorem for theBenchmark
% 2.44/0.69  % SZS output start Proof for theBenchmark
% 2.44/0.69  fof(f1173,plain,(
% 2.44/0.69    $false),
% 2.44/0.69    inference(avatar_sat_refutation,[],[f61,f199,f1099,f1146,f1166,f1172])).
% 2.44/0.69  fof(f1172,plain,(
% 2.44/0.69    spl2_1 | ~spl2_7),
% 2.44/0.69    inference(avatar_contradiction_clause,[],[f1169])).
% 2.44/0.69  fof(f1169,plain,(
% 2.44/0.69    $false | (spl2_1 | ~spl2_7)),
% 2.44/0.69    inference(unit_resulting_resolution,[],[f60,f1165,f54])).
% 2.44/0.69  fof(f54,plain,(
% 2.44/0.69    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 2.44/0.69    inference(definition_unfolding,[],[f35,f51,f51])).
% 2.44/0.69  fof(f51,plain,(
% 2.44/0.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.44/0.69    inference(definition_unfolding,[],[f36,f50])).
% 2.44/0.69  fof(f50,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.44/0.69    inference(definition_unfolding,[],[f45,f48])).
% 2.44/0.69  fof(f48,plain,(
% 2.44/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f15])).
% 2.44/0.69  fof(f15,axiom,(
% 2.44/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.44/0.69  fof(f45,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f14])).
% 2.44/0.69  fof(f14,axiom,(
% 2.44/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.44/0.69  fof(f36,plain,(
% 2.44/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f13])).
% 2.44/0.69  fof(f13,axiom,(
% 2.44/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.44/0.69  fof(f35,plain,(
% 2.44/0.69    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 2.44/0.69    inference(cnf_transformation,[],[f26])).
% 2.44/0.69  fof(f26,plain,(
% 2.44/0.69    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.44/0.69    inference(ennf_transformation,[],[f20])).
% 2.44/0.69  fof(f20,axiom,(
% 2.44/0.69    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.44/0.69  fof(f1165,plain,(
% 2.44/0.69    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_7),
% 2.44/0.69    inference(avatar_component_clause,[],[f1163])).
% 2.44/0.69  fof(f1163,plain,(
% 2.44/0.69    spl2_7 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.44/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.44/0.69  fof(f60,plain,(
% 2.44/0.69    sK0 != sK1 | spl2_1),
% 2.44/0.69    inference(avatar_component_clause,[],[f58])).
% 2.44/0.69  fof(f58,plain,(
% 2.44/0.69    spl2_1 <=> sK0 = sK1),
% 2.44/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.44/0.69  fof(f1166,plain,(
% 2.44/0.69    spl2_7 | ~spl2_6),
% 2.44/0.69    inference(avatar_split_clause,[],[f1152,f1142,f1163])).
% 2.44/0.69  fof(f1142,plain,(
% 2.44/0.69    spl2_6 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.44/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.44/0.69  fof(f1152,plain,(
% 2.44/0.69    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_6),
% 2.44/0.69    inference(superposition,[],[f44,f1144])).
% 2.44/0.69  fof(f1144,plain,(
% 2.44/0.69    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_6),
% 2.44/0.69    inference(avatar_component_clause,[],[f1142])).
% 2.44/0.69  fof(f44,plain,(
% 2.44/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f6])).
% 2.44/0.69  fof(f6,axiom,(
% 2.44/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.44/0.69  fof(f1146,plain,(
% 2.44/0.69    spl2_6 | ~spl2_5),
% 2.44/0.69    inference(avatar_split_clause,[],[f1138,f1096,f1142])).
% 2.44/0.69  fof(f1096,plain,(
% 2.44/0.69    spl2_5 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 2.44/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.44/0.69  fof(f1138,plain,(
% 2.44/0.69    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_5),
% 2.44/0.69    inference(forward_demodulation,[],[f1119,f63])).
% 2.44/0.69  fof(f63,plain,(
% 2.44/0.69    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.44/0.69    inference(superposition,[],[f39,f40])).
% 2.44/0.69  fof(f40,plain,(
% 2.44/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.44/0.69    inference(cnf_transformation,[],[f10])).
% 2.44/0.69  fof(f10,axiom,(
% 2.44/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.44/0.69  fof(f39,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f2])).
% 2.44/0.69  fof(f2,axiom,(
% 2.44/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.44/0.69  fof(f1119,plain,(
% 2.44/0.69    k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_5),
% 2.44/0.69    inference(superposition,[],[f799,f1098])).
% 2.44/0.69  fof(f1098,plain,(
% 2.44/0.69    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl2_5),
% 2.44/0.69    inference(avatar_component_clause,[],[f1096])).
% 2.44/0.69  fof(f799,plain,(
% 2.44/0.69    ( ! [X31,X32] : (k5_xboole_0(k5_xboole_0(X31,X32),X31) = X32) )),
% 2.44/0.69    inference(forward_demodulation,[],[f782,f63])).
% 2.44/0.69  fof(f782,plain,(
% 2.44/0.69    ( ! [X31,X32] : (k5_xboole_0(k5_xboole_0(X31,X32),X31) = k5_xboole_0(k1_xboole_0,X32)) )),
% 2.44/0.69    inference(superposition,[],[f350,f678])).
% 2.44/0.69  fof(f678,plain,(
% 2.44/0.69    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X7,X8)) = X8) )),
% 2.44/0.69    inference(forward_demodulation,[],[f662,f63])).
% 2.44/0.69  fof(f662,plain,(
% 2.44/0.69    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X7,X8)) = k5_xboole_0(k1_xboole_0,X8)) )),
% 2.44/0.69    inference(superposition,[],[f37,f651])).
% 2.44/0.69  fof(f651,plain,(
% 2.44/0.69    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 2.44/0.69    inference(global_subsumption,[],[f76,f650])).
% 2.44/0.69  fof(f650,plain,(
% 2.44/0.69    ( ! [X5] : (~r1_tarski(k5_xboole_0(X5,X5),X5) | k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 2.44/0.69    inference(duplicate_literal_removal,[],[f638])).
% 2.44/0.69  fof(f638,plain,(
% 2.44/0.69    ( ! [X5] : (~r1_tarski(k5_xboole_0(X5,X5),X5) | k1_xboole_0 = k5_xboole_0(X5,X5) | ~r1_tarski(k5_xboole_0(X5,X5),X5)) )),
% 2.44/0.69    inference(superposition,[],[f115,f104])).
% 2.44/0.69  fof(f104,plain,(
% 2.44/0.69    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 2.44/0.69    inference(forward_demodulation,[],[f53,f47])).
% 2.44/0.69  fof(f47,plain,(
% 2.44/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.44/0.69    inference(cnf_transformation,[],[f24])).
% 2.44/0.69  fof(f24,plain,(
% 2.44/0.69    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.44/0.69    inference(rectify,[],[f4])).
% 2.44/0.69  fof(f4,axiom,(
% 2.44/0.69    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.44/0.69  fof(f53,plain,(
% 2.44/0.69    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.44/0.69    inference(definition_unfolding,[],[f34,f49])).
% 2.44/0.69  fof(f49,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.44/0.69    inference(definition_unfolding,[],[f33,f38])).
% 2.44/0.69  fof(f38,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.44/0.69    inference(cnf_transformation,[],[f5])).
% 2.44/0.69  fof(f5,axiom,(
% 2.44/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.44/0.69  fof(f33,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.44/0.69    inference(cnf_transformation,[],[f12])).
% 2.44/0.69  fof(f12,axiom,(
% 2.44/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.44/0.69  fof(f34,plain,(
% 2.44/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.44/0.69    inference(cnf_transformation,[],[f23])).
% 2.44/0.69  fof(f23,plain,(
% 2.44/0.69    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.44/0.69    inference(rectify,[],[f3])).
% 2.44/0.69  fof(f3,axiom,(
% 2.44/0.69    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.44/0.69  fof(f115,plain,(
% 2.44/0.69    ( ! [X2,X1] : (~r1_tarski(X2,k5_xboole_0(X1,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X1)) )),
% 2.44/0.69    inference(superposition,[],[f55,f82])).
% 2.44/0.69  fof(f82,plain,(
% 2.44/0.69    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = X3 | ~r1_tarski(X3,X4)) )),
% 2.44/0.69    inference(superposition,[],[f43,f46])).
% 2.44/0.69  fof(f46,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f1])).
% 2.44/0.69  fof(f1,axiom,(
% 2.44/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.44/0.69  fof(f43,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f28])).
% 2.44/0.69  fof(f28,plain,(
% 2.44/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.44/0.69    inference(ennf_transformation,[],[f7])).
% 2.44/0.69  fof(f7,axiom,(
% 2.44/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.44/0.69  fof(f55,plain,(
% 2.44/0.69    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0) )),
% 2.44/0.69    inference(definition_unfolding,[],[f41,f38])).
% 2.44/0.69  fof(f41,plain,(
% 2.44/0.69    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.44/0.69    inference(cnf_transformation,[],[f27])).
% 2.44/0.69  fof(f27,plain,(
% 2.44/0.69    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.44/0.69    inference(ennf_transformation,[],[f9])).
% 2.44/0.69  fof(f9,axiom,(
% 2.44/0.69    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 2.44/0.69  fof(f76,plain,(
% 2.44/0.69    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 2.44/0.69    inference(superposition,[],[f56,f47])).
% 2.44/0.69  fof(f56,plain,(
% 2.44/0.69    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.44/0.69    inference(definition_unfolding,[],[f42,f38])).
% 2.44/0.69  fof(f42,plain,(
% 2.44/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.44/0.69    inference(cnf_transformation,[],[f8])).
% 2.44/0.69  fof(f8,axiom,(
% 2.44/0.69    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.44/0.69  fof(f37,plain,(
% 2.44/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.44/0.69    inference(cnf_transformation,[],[f11])).
% 2.44/0.69  fof(f11,axiom,(
% 2.44/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.44/0.69  fof(f350,plain,(
% 2.44/0.69    ( ! [X26,X27] : (k5_xboole_0(X27,X26) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X26,X27))) )),
% 2.44/0.69    inference(superposition,[],[f144,f63])).
% 2.44/0.69  fof(f144,plain,(
% 2.44/0.69    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 2.44/0.69    inference(superposition,[],[f37,f39])).
% 2.44/0.69  fof(f1099,plain,(
% 2.44/0.69    spl2_5 | ~spl2_2),
% 2.44/0.69    inference(avatar_split_clause,[],[f789,f196,f1096])).
% 2.44/0.69  fof(f196,plain,(
% 2.44/0.69    spl2_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))))),
% 2.44/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.44/0.69  fof(f789,plain,(
% 2.44/0.69    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl2_2),
% 2.44/0.69    inference(forward_demodulation,[],[f764,f651])).
% 2.44/0.69  fof(f764,plain,(
% 2.44/0.69    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_2),
% 2.44/0.69    inference(superposition,[],[f678,f198])).
% 2.44/0.69  fof(f198,plain,(
% 2.44/0.69    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))) | ~spl2_2),
% 2.44/0.69    inference(avatar_component_clause,[],[f196])).
% 2.44/0.69  fof(f199,plain,(
% 2.44/0.69    spl2_2),
% 2.44/0.69    inference(avatar_split_clause,[],[f194,f196])).
% 2.44/0.69  fof(f194,plain,(
% 2.44/0.69    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))))),
% 2.44/0.69    inference(forward_demodulation,[],[f52,f46])).
% 2.44/0.69  fof(f52,plain,(
% 2.44/0.69    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.44/0.69    inference(definition_unfolding,[],[f31,f51,f49,f51,f51])).
% 2.44/0.69  fof(f31,plain,(
% 2.44/0.69    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.44/0.69    inference(cnf_transformation,[],[f30])).
% 2.44/0.69  fof(f30,plain,(
% 2.44/0.69    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.44/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).
% 2.44/0.69  fof(f29,plain,(
% 2.44/0.69    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.44/0.69    introduced(choice_axiom,[])).
% 2.44/0.69  fof(f25,plain,(
% 2.44/0.69    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.44/0.69    inference(ennf_transformation,[],[f22])).
% 2.44/0.69  fof(f22,negated_conjecture,(
% 2.44/0.69    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.44/0.69    inference(negated_conjecture,[],[f21])).
% 2.44/0.69  fof(f21,conjecture,(
% 2.44/0.69    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.44/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.44/0.69  fof(f61,plain,(
% 2.44/0.69    ~spl2_1),
% 2.44/0.69    inference(avatar_split_clause,[],[f32,f58])).
% 2.44/0.69  fof(f32,plain,(
% 2.44/0.69    sK0 != sK1),
% 2.44/0.69    inference(cnf_transformation,[],[f30])).
% 2.44/0.69  % SZS output end Proof for theBenchmark
% 2.44/0.69  % (31354)------------------------------
% 2.44/0.69  % (31354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.69  % (31354)Termination reason: Refutation
% 2.44/0.69  
% 2.44/0.69  % (31354)Memory used [KB]: 11769
% 2.44/0.69  % (31354)Time elapsed: 0.202 s
% 2.44/0.69  % (31354)------------------------------
% 2.44/0.69  % (31354)------------------------------
% 2.44/0.69  % (31330)Success in time 0.325 s
%------------------------------------------------------------------------------
