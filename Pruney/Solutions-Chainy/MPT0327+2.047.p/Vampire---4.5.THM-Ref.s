%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:55 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 498 expanded)
%              Number of leaves         :   28 ( 174 expanded)
%              Depth                    :   18
%              Number of atoms          :  168 ( 654 expanded)
%              Number of equality atoms :   93 ( 455 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f129,f145,f493,f1196,f1387,f2122,f2183])).

fof(f2183,plain,
    ( k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | sK1 = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2122,plain,
    ( spl2_43
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f2117,f135,f2119])).

fof(f2119,plain,
    ( spl2_43
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f135,plain,
    ( spl2_4
  <=> k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2117,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f2116,f387])).

fof(f387,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f76,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(unit_resulting_resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f30,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = X0 ),
    inference(unit_resulting_resolution,[],[f30,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2116,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f2115,f1251])).

fof(f1251,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f1250,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1250,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f1249,f447])).

fof(f447,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f437,f387])).

fof(f437,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f53,f399])).

fof(f399,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(X8,X8) ),
    inference(superposition,[],[f73,f387])).

fof(f73,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f32,f43])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1249,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(forward_demodulation,[],[f1208,f387])).

fof(f1208,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f1181,f399])).

fof(f1181,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f56,f1179])).

fof(f1179,plain,(
    ! [X2,X3] : k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f220,f98])).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f37,f37])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f220,plain,(
    ! [X2,X3] : k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f56,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f51,f37])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f2115,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f2114,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f82,f43])).

fof(f82,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f32,f72])).

fof(f2114,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f2049,f55])).

fof(f2049,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))))
    | ~ spl2_4 ),
    inference(superposition,[],[f1233,f137])).

fof(f137,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1233,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f1232,f53])).

fof(f1232,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(forward_demodulation,[],[f1200,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f46,f37,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1200,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)) ),
    inference(superposition,[],[f1181,f53])).

fof(f1387,plain,
    ( spl2_25
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1382,f135,f1384])).

fof(f1384,plain,
    ( spl2_25
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f1382,plain,
    ( sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f1381,f387])).

fof(f1381,plain,
    ( sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f1326,f29])).

fof(f1326,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_4 ),
    inference(superposition,[],[f1180,f137])).

fof(f1180,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f216,f1179])).

fof(f216,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f56,f55])).

fof(f1196,plain,
    ( ~ spl2_23
    | spl2_1 ),
    inference(avatar_split_clause,[],[f1185,f63,f1193])).

fof(f1193,plain,
    ( spl2_23
  <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f63,plain,
    ( spl2_1
  <=> sK1 = k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1185,plain,
    ( sK1 != k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | spl2_1 ),
    inference(superposition,[],[f65,f1179])).

fof(f65,plain,
    ( sK1 != k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f493,plain,
    ( spl2_11
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f488,f135,f490])).

fof(f490,plain,
    ( spl2_11
  <=> k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f488,plain,
    ( k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f466,f387])).

fof(f466,plain,
    ( k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))
    | ~ spl2_4 ),
    inference(superposition,[],[f98,f137])).

fof(f145,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f133,f125,f135])).

fof(f125,plain,
    ( spl2_3
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f133,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f127,f43])).

fof(f127,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f129,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f123,f68,f125])).

fof(f68,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f123,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f58,f70])).

fof(f70,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f71,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f66,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f54,f63])).

fof(f54,plain,(
    sK1 != k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f28,f51,f52,f52])).

fof(f28,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (26607)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (26599)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (26611)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (26601)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (26603)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (26614)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (26604)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (26605)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (26597)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (26600)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (26602)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (26598)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (26608)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (26606)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (26609)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (26608)Refutation not found, incomplete strategy% (26608)------------------------------
% 0.21/0.50  % (26608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26608)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26608)Memory used [KB]: 10618
% 0.21/0.50  % (26608)Time elapsed: 0.083 s
% 0.21/0.50  % (26608)------------------------------
% 0.21/0.50  % (26608)------------------------------
% 0.21/0.51  % (26610)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (26612)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (26613)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.54/0.56  % (26603)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f2184,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(avatar_sat_refutation,[],[f66,f71,f129,f145,f493,f1196,f1387,f2122,f2183])).
% 1.54/0.56  fof(f2183,plain,(
% 1.54/0.56    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | sK1 = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.54/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.56  fof(f2122,plain,(
% 1.54/0.56    spl2_43 | ~spl2_4),
% 1.54/0.56    inference(avatar_split_clause,[],[f2117,f135,f2119])).
% 1.54/0.56  fof(f2119,plain,(
% 1.54/0.56    spl2_43 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 1.54/0.56  fof(f135,plain,(
% 1.54/0.56    spl2_4 <=> k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.54/0.56  fof(f2117,plain,(
% 1.54/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f2116,f387])).
% 1.54/0.56  fof(f387,plain,(
% 1.54/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(forward_demodulation,[],[f76,f72])).
% 1.54/0.56  fof(f72,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f30,f43])).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f26])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.54/0.56    inference(nnf_transformation,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f18])).
% 1.54/0.56  fof(f18,axiom,(
% 1.54/0.56    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.54/0.56  fof(f76,plain,(
% 1.54/0.56    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = X0) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f30,f57])).
% 1.54/0.56  fof(f57,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.54/0.56    inference(definition_unfolding,[],[f39,f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f22])).
% 1.54/0.56  fof(f22,plain,(
% 1.54/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.56  fof(f2116,plain,(
% 1.54/0.56    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f2115,f1251])).
% 1.54/0.56  fof(f1251,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.56    inference(forward_demodulation,[],[f1250,f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.54/0.56  fof(f1250,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f1249,f447])).
% 1.54/0.56  fof(f447,plain,(
% 1.54/0.56    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f437,f387])).
% 1.54/0.56  fof(f437,plain,(
% 1.54/0.56    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 1.54/0.56    inference(superposition,[],[f53,f399])).
% 1.54/0.56  fof(f399,plain,(
% 1.54/0.56    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(X8,X8)) )),
% 1.54/0.56    inference(superposition,[],[f73,f387])).
% 1.54/0.56  fof(f73,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f32,f43])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.54/0.56  fof(f53,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f36,f37])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.56  fof(f1249,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f1208,f387])).
% 1.54/0.56  fof(f1208,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0))) )),
% 1.54/0.56    inference(superposition,[],[f1181,f399])).
% 1.54/0.56  fof(f1181,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.56    inference(backward_demodulation,[],[f56,f1179])).
% 1.54/0.56  fof(f1179,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f220,f98])).
% 1.54/0.56  fof(f98,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.54/0.56    inference(superposition,[],[f53,f55])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f33,f37,f37])).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.56  fof(f220,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) )),
% 1.54/0.56    inference(superposition,[],[f56,f45])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.56  fof(f56,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f38,f51,f37])).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f34,f50])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f35,f49])).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f44,f48])).
% 1.54/0.56  fof(f48,plain,(
% 1.54/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f14])).
% 1.54/0.56  fof(f14,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f13])).
% 1.54/0.56  fof(f13,axiom,(
% 1.54/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,axiom,(
% 1.54/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  fof(f11,axiom,(
% 1.54/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.54/0.56  fof(f2115,plain,(
% 1.54/0.56    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f2114,f95])).
% 1.54/0.56  fof(f95,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f82,f43])).
% 1.54/0.56  fof(f82,plain,(
% 1.54/0.56    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.54/0.56    inference(superposition,[],[f32,f72])).
% 1.54/0.56  fof(f2114,plain,(
% 1.54/0.56    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f2049,f55])).
% 1.54/0.56  fof(f2049,plain,(
% 1.54/0.56    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)))) | ~spl2_4),
% 1.54/0.56    inference(superposition,[],[f1233,f137])).
% 1.54/0.56  fof(f137,plain,(
% 1.54/0.56    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl2_4),
% 1.54/0.56    inference(avatar_component_clause,[],[f135])).
% 1.54/0.56  fof(f1233,plain,(
% 1.54/0.56    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f1232,f53])).
% 1.54/0.56  fof(f1232,plain,(
% 1.54/0.56    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f1200,f60])).
% 1.54/0.56  fof(f60,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f46,f37,f37])).
% 1.54/0.56  fof(f46,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.54/0.56  fof(f1200,plain,(
% 1.54/0.56    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1))) )),
% 1.54/0.56    inference(superposition,[],[f1181,f53])).
% 1.54/0.56  fof(f1387,plain,(
% 1.54/0.56    spl2_25 | ~spl2_4),
% 1.54/0.56    inference(avatar_split_clause,[],[f1382,f135,f1384])).
% 1.54/0.56  fof(f1384,plain,(
% 1.54/0.56    spl2_25 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 1.54/0.56  fof(f1382,plain,(
% 1.54/0.56    sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f1381,f387])).
% 1.54/0.56  fof(f1381,plain,(
% 1.54/0.56    sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f1326,f29])).
% 1.54/0.56  fof(f1326,plain,(
% 1.54/0.56    k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_4),
% 1.54/0.56    inference(superposition,[],[f1180,f137])).
% 1.54/0.56  fof(f1180,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.56    inference(backward_demodulation,[],[f216,f1179])).
% 1.54/0.56  fof(f216,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.54/0.56    inference(superposition,[],[f56,f55])).
% 1.54/0.56  fof(f1196,plain,(
% 1.54/0.56    ~spl2_23 | spl2_1),
% 1.54/0.56    inference(avatar_split_clause,[],[f1185,f63,f1193])).
% 1.54/0.56  fof(f1193,plain,(
% 1.54/0.56    spl2_23 <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    spl2_1 <=> sK1 = k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.54/0.56  fof(f1185,plain,(
% 1.54/0.56    sK1 != k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | spl2_1),
% 1.54/0.56    inference(superposition,[],[f65,f1179])).
% 1.54/0.56  fof(f65,plain,(
% 1.54/0.56    sK1 != k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl2_1),
% 1.54/0.56    inference(avatar_component_clause,[],[f63])).
% 1.54/0.56  fof(f493,plain,(
% 1.54/0.56    spl2_11 | ~spl2_4),
% 1.54/0.56    inference(avatar_split_clause,[],[f488,f135,f490])).
% 1.54/0.56  fof(f490,plain,(
% 1.54/0.56    spl2_11 <=> k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.54/0.56  fof(f488,plain,(
% 1.54/0.56    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 1.54/0.56    inference(forward_demodulation,[],[f466,f387])).
% 1.54/0.56  fof(f466,plain,(
% 1.54/0.56    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) | ~spl2_4),
% 1.54/0.56    inference(superposition,[],[f98,f137])).
% 1.54/0.56  fof(f145,plain,(
% 1.54/0.56    spl2_4 | ~spl2_3),
% 1.54/0.56    inference(avatar_split_clause,[],[f133,f125,f135])).
% 1.54/0.56  fof(f125,plain,(
% 1.54/0.56    spl2_3 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.54/0.56  fof(f133,plain,(
% 1.54/0.56    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl2_3),
% 1.54/0.56    inference(resolution,[],[f127,f43])).
% 1.54/0.56  fof(f127,plain,(
% 1.54/0.56    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl2_3),
% 1.54/0.56    inference(avatar_component_clause,[],[f125])).
% 1.54/0.56  fof(f129,plain,(
% 1.54/0.56    spl2_3 | ~spl2_2),
% 1.54/0.56    inference(avatar_split_clause,[],[f123,f68,f125])).
% 1.54/0.56  fof(f68,plain,(
% 1.54/0.56    spl2_2 <=> r2_hidden(sK0,sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.54/0.56  fof(f123,plain,(
% 1.54/0.56    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl2_2),
% 1.54/0.56    inference(resolution,[],[f58,f70])).
% 1.54/0.56  fof(f70,plain,(
% 1.54/0.56    r2_hidden(sK0,sK1) | ~spl2_2),
% 1.54/0.56    inference(avatar_component_clause,[],[f68])).
% 1.54/0.56  fof(f58,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f41,f52])).
% 1.54/0.56  fof(f52,plain,(
% 1.54/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f31,f50])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,axiom,(
% 1.54/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.54/0.56    inference(nnf_transformation,[],[f16])).
% 1.54/0.56  fof(f16,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.54/0.56  fof(f71,plain,(
% 1.54/0.56    spl2_2),
% 1.54/0.56    inference(avatar_split_clause,[],[f27,f68])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,negated_conjecture,(
% 1.54/0.56    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.54/0.56    inference(negated_conjecture,[],[f19])).
% 1.54/0.56  fof(f19,conjecture,(
% 1.54/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.54/0.56  fof(f66,plain,(
% 1.54/0.56    ~spl2_1),
% 1.54/0.56    inference(avatar_split_clause,[],[f54,f63])).
% 1.54/0.56  fof(f54,plain,(
% 1.54/0.56    sK1 != k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.56    inference(definition_unfolding,[],[f28,f51,f52,f52])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.54/0.56    inference(cnf_transformation,[],[f24])).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (26603)------------------------------
% 1.54/0.56  % (26603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (26603)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (26603)Memory used [KB]: 7803
% 1.54/0.56  % (26603)Time elapsed: 0.100 s
% 1.54/0.56  % (26603)------------------------------
% 1.54/0.56  % (26603)------------------------------
% 1.54/0.56  % (26596)Success in time 0.202 s
%------------------------------------------------------------------------------
