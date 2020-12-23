%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:09 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 323 expanded)
%              Number of leaves         :   31 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 451 expanded)
%              Number of equality atoms :   91 ( 289 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f85,f100,f101,f111,f171,f943,f1215,f1285,f1287])).

fof(f1287,plain,
    ( sK0 != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 != k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1285,plain,
    ( ~ spl3_12
    | ~ spl3_53 ),
    inference(avatar_contradiction_clause,[],[f1284])).

fof(f1284,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f1268,f589])).

fof(f589,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f450,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f450,plain,
    ( ! [X10] : r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X10)),k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f38,f206])).

fof(f206,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,X1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f66,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_12
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f49,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1268,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl3_53 ),
    inference(superposition,[],[f67,f1214])).

fof(f1214,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f1212,plain,
    ( spl3_53
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f67,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f46,f60,f40,f60,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1215,plain,
    ( spl3_53
    | ~ spl3_3
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f1193,f940,f81,f1212])).

fof(f81,plain,
    ( spl3_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f940,plain,
    ( spl3_47
  <=> k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1193,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_3
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f83,f942])).

fof(f942,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f940])).

fof(f83,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f943,plain,
    ( spl3_30
    | spl3_47
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f919,f168,f107,f940,f516])).

fof(f516,plain,
    ( spl3_30
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f107,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f919,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f767,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f60,f40,f59,f60])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f767,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1)))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f136,f589])).

fof(f136,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1)))
    | ~ spl3_6 ),
    inference(superposition,[],[f66,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f171,plain,
    ( spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f166,f96,f168])).

fof(f96,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f166,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f147,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f147,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f113,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f113,plain,
    ( ! [X0] : k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_5 ),
    inference(superposition,[],[f50,f98])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f111,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f104,f91,f107])).

fof(f91,plain,
    ( spl3_4
  <=> r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f104,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f93,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f93,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f101,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f89,f74,f91])).

fof(f74,plain,
    ( spl3_2
  <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f76,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f100,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f88,f74,f96])).

fof(f88,plain,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f44])).

fof(f85,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f79,f69,f81])).

fof(f69,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f71,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f60,f60])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f71,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f61,f74])).

fof(f61,plain,(
    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f32,plain,(
    r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( r2_hidden(sK0,sK2)
    & r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) )
   => ( r2_hidden(sK0,sK2)
      & r1_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X0,X2)
          & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f72,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:13:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (10573)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (10587)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (10575)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10587)Refutation not found, incomplete strategy% (10587)------------------------------
% 0.21/0.51  % (10587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10587)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10587)Memory used [KB]: 6140
% 0.21/0.51  % (10587)Time elapsed: 0.004 s
% 0.21/0.51  % (10587)------------------------------
% 0.21/0.51  % (10587)------------------------------
% 0.21/0.51  % (10588)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (10580)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10582)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (10582)Refutation not found, incomplete strategy% (10582)------------------------------
% 0.21/0.52  % (10582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10582)Memory used [KB]: 10618
% 0.21/0.52  % (10582)Time elapsed: 0.116 s
% 0.21/0.52  % (10582)------------------------------
% 0.21/0.52  % (10582)------------------------------
% 0.21/0.53  % (10596)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (10590)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (10599)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10576)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (10597)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (10581)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (10591)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (10589)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (10589)Refutation not found, incomplete strategy% (10589)------------------------------
% 0.21/0.55  % (10589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10572)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (10583)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (10589)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10589)Memory used [KB]: 10618
% 0.21/0.55  % (10589)Time elapsed: 0.127 s
% 0.21/0.55  % (10589)------------------------------
% 0.21/0.55  % (10589)------------------------------
% 0.21/0.55  % (10579)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (10583)Refutation not found, incomplete strategy% (10583)------------------------------
% 0.21/0.55  % (10583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10583)Memory used [KB]: 10618
% 0.21/0.55  % (10583)Time elapsed: 0.147 s
% 0.21/0.55  % (10583)------------------------------
% 0.21/0.55  % (10583)------------------------------
% 1.45/0.56  % (10577)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.56  % (10595)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (10574)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.57  % (10598)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.57  % (10585)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.57  % (10592)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.67/0.58  % (10584)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.67/0.58  % (10586)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.67/0.58  % (10601)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.67/0.58  % (10593)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.67/0.59  % (10578)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.67/0.59  % (10594)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.67/0.59  % (10594)Refutation not found, incomplete strategy% (10594)------------------------------
% 1.67/0.59  % (10594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (10594)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.59  % (10600)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.67/0.59  
% 1.67/0.59  % (10594)Memory used [KB]: 10618
% 1.67/0.59  % (10594)Time elapsed: 0.177 s
% 1.67/0.59  % (10594)------------------------------
% 1.67/0.59  % (10594)------------------------------
% 1.67/0.59  % (10597)Refutation found. Thanks to Tanya!
% 1.67/0.59  % SZS status Theorem for theBenchmark
% 1.67/0.59  % SZS output start Proof for theBenchmark
% 1.67/0.60  fof(f1288,plain,(
% 1.67/0.60    $false),
% 1.67/0.60    inference(avatar_sat_refutation,[],[f72,f77,f85,f100,f101,f111,f171,f943,f1215,f1285,f1287])).
% 1.67/0.60  fof(f1287,plain,(
% 1.67/0.60    sK0 != sK1 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 != k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.67/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.67/0.60  fof(f1285,plain,(
% 1.67/0.60    ~spl3_12 | ~spl3_53),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f1284])).
% 1.67/0.60  fof(f1284,plain,(
% 1.67/0.60    $false | (~spl3_12 | ~spl3_53)),
% 1.67/0.60    inference(subsumption_resolution,[],[f1268,f589])).
% 1.67/0.60  fof(f589,plain,(
% 1.67/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | ~spl3_12),
% 1.67/0.60    inference(unit_resulting_resolution,[],[f450,f36])).
% 1.67/0.60  fof(f36,plain,(
% 1.67/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f24])).
% 1.67/0.60  fof(f24,plain,(
% 1.67/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.67/0.60    inference(ennf_transformation,[],[f7])).
% 1.67/0.60  fof(f7,axiom,(
% 1.67/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.67/0.60  fof(f450,plain,(
% 1.67/0.60    ( ! [X10] : (r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X10)),k1_xboole_0)) ) | ~spl3_12),
% 1.67/0.60    inference(superposition,[],[f38,f206])).
% 1.67/0.60  fof(f206,plain,(
% 1.67/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,X1)))) ) | ~spl3_12),
% 1.67/0.60    inference(superposition,[],[f66,f170])).
% 1.67/0.60  fof(f170,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl3_12),
% 1.67/0.60    inference(avatar_component_clause,[],[f168])).
% 1.67/0.60  fof(f168,plain,(
% 1.67/0.60    spl3_12 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.67/0.60  fof(f66,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.67/0.60    inference(definition_unfolding,[],[f49,f40,f40])).
% 1.67/0.60  fof(f40,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f4])).
% 1.67/0.60  fof(f4,axiom,(
% 1.67/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.60  fof(f49,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f8])).
% 1.67/0.60  fof(f8,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.67/0.60  fof(f38,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f6])).
% 1.67/0.60  fof(f6,axiom,(
% 1.67/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.67/0.60  fof(f1268,plain,(
% 1.67/0.60    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl3_53),
% 1.67/0.60    inference(superposition,[],[f67,f1214])).
% 1.67/0.60  fof(f1214,plain,(
% 1.67/0.60    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_53),
% 1.67/0.60    inference(avatar_component_clause,[],[f1212])).
% 1.67/0.60  fof(f1212,plain,(
% 1.67/0.60    spl3_53 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 1.67/0.60  fof(f67,plain,(
% 1.67/0.60    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 1.67/0.60    inference(equality_resolution,[],[f65])).
% 1.67/0.60  fof(f65,plain,(
% 1.67/0.60    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 1.67/0.60    inference(definition_unfolding,[],[f46,f60,f40,f60,f60])).
% 1.67/0.60  fof(f60,plain,(
% 1.67/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f35,f59])).
% 1.67/0.60  fof(f59,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f39,f58])).
% 1.67/0.60  fof(f58,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f48,f57])).
% 1.67/0.60  fof(f57,plain,(
% 1.67/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f51,f56])).
% 1.67/0.60  fof(f56,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f52,f55])).
% 1.67/0.60  fof(f55,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f53,f54])).
% 1.67/0.60  fof(f54,plain,(
% 1.67/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f16])).
% 1.67/0.60  fof(f16,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.67/0.60  fof(f53,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f15])).
% 1.67/0.60  fof(f15,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.67/0.60  fof(f52,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f14])).
% 1.67/0.60  fof(f14,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.67/0.60  fof(f51,plain,(
% 1.67/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f13])).
% 1.67/0.60  fof(f13,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.67/0.60  fof(f48,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f12])).
% 1.67/0.60  fof(f12,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.67/0.60  fof(f39,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f11])).
% 1.67/0.60  fof(f11,axiom,(
% 1.67/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.60  fof(f35,plain,(
% 1.67/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f10])).
% 1.67/0.60  fof(f10,axiom,(
% 1.67/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.67/0.60  fof(f46,plain,(
% 1.67/0.60    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f31])).
% 1.67/0.60  fof(f31,plain,(
% 1.67/0.60    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.67/0.60    inference(nnf_transformation,[],[f18])).
% 1.67/0.60  fof(f18,axiom,(
% 1.67/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.67/0.60  fof(f1215,plain,(
% 1.67/0.60    spl3_53 | ~spl3_3 | ~spl3_47),
% 1.67/0.60    inference(avatar_split_clause,[],[f1193,f940,f81,f1212])).
% 1.67/0.60  fof(f81,plain,(
% 1.67/0.60    spl3_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.67/0.60  fof(f940,plain,(
% 1.67/0.60    spl3_47 <=> k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.67/0.60  fof(f1193,plain,(
% 1.67/0.60    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl3_3 | ~spl3_47)),
% 1.67/0.60    inference(backward_demodulation,[],[f83,f942])).
% 1.67/0.60  fof(f942,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_47),
% 1.67/0.60    inference(avatar_component_clause,[],[f940])).
% 1.67/0.60  fof(f83,plain,(
% 1.67/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_3),
% 1.67/0.60    inference(avatar_component_clause,[],[f81])).
% 1.67/0.60  fof(f943,plain,(
% 1.67/0.60    spl3_30 | spl3_47 | ~spl3_6 | ~spl3_12),
% 1.67/0.60    inference(avatar_split_clause,[],[f919,f168,f107,f940,f516])).
% 1.67/0.60  fof(f516,plain,(
% 1.67/0.60    spl3_30 <=> sK0 = sK1),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.67/0.60  fof(f107,plain,(
% 1.67/0.60    spl3_6 <=> k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.67/0.60  fof(f919,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK1 | (~spl3_6 | ~spl3_12)),
% 1.67/0.60    inference(superposition,[],[f767,f62])).
% 1.67/0.60  fof(f62,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) | X0 = X1) )),
% 1.67/0.60    inference(definition_unfolding,[],[f41,f60,f40,f59,f60])).
% 1.67/0.60  fof(f41,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1) )),
% 1.67/0.60    inference(cnf_transformation,[],[f25])).
% 1.67/0.60  fof(f25,plain,(
% 1.67/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1)),
% 1.67/0.60    inference(ennf_transformation,[],[f19])).
% 1.67/0.60  fof(f19,axiom,(
% 1.67/0.60    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 1.67/0.60  fof(f767,plain,(
% 1.67/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1)))) ) | (~spl3_6 | ~spl3_12)),
% 1.67/0.60    inference(backward_demodulation,[],[f136,f589])).
% 1.67/0.60  fof(f136,plain,(
% 1.67/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1)))) ) | ~spl3_6),
% 1.67/0.60    inference(superposition,[],[f66,f109])).
% 1.67/0.60  fof(f109,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_6),
% 1.67/0.60    inference(avatar_component_clause,[],[f107])).
% 1.67/0.60  fof(f171,plain,(
% 1.67/0.60    spl3_12 | ~spl3_5),
% 1.67/0.60    inference(avatar_split_clause,[],[f166,f96,f168])).
% 1.67/0.60  fof(f96,plain,(
% 1.67/0.60    spl3_5 <=> k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.67/0.60  fof(f166,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl3_5),
% 1.67/0.60    inference(forward_demodulation,[],[f147,f98])).
% 1.67/0.60  fof(f98,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_5),
% 1.67/0.60    inference(avatar_component_clause,[],[f96])).
% 1.67/0.60  fof(f147,plain,(
% 1.67/0.60    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k3_xboole_0(k1_xboole_0,sK2) | ~spl3_5),
% 1.67/0.60    inference(superposition,[],[f113,f37])).
% 1.67/0.60  fof(f37,plain,(
% 1.67/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.67/0.60    inference(cnf_transformation,[],[f22])).
% 1.67/0.60  fof(f22,plain,(
% 1.67/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.67/0.60    inference(rectify,[],[f2])).
% 1.67/0.60  fof(f2,axiom,(
% 1.67/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.67/0.60  fof(f113,plain,(
% 1.67/0.60    ( ! [X0] : (k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_5),
% 1.67/0.60    inference(superposition,[],[f50,f98])).
% 1.67/0.60  fof(f50,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f5])).
% 1.67/0.60  fof(f5,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.67/0.60  fof(f111,plain,(
% 1.67/0.60    spl3_6 | ~spl3_4),
% 1.67/0.60    inference(avatar_split_clause,[],[f104,f91,f107])).
% 1.67/0.60  fof(f91,plain,(
% 1.67/0.60    spl3_4 <=> r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.67/0.60  fof(f104,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_4),
% 1.67/0.60    inference(resolution,[],[f93,f44])).
% 1.67/0.60  fof(f44,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f30])).
% 1.67/0.60  fof(f30,plain,(
% 1.67/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.67/0.60    inference(nnf_transformation,[],[f1])).
% 1.67/0.60  fof(f1,axiom,(
% 1.67/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.67/0.60  fof(f93,plain,(
% 1.67/0.60    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_4),
% 1.67/0.60    inference(avatar_component_clause,[],[f91])).
% 1.67/0.60  fof(f101,plain,(
% 1.67/0.60    spl3_4 | ~spl3_2),
% 1.67/0.60    inference(avatar_split_clause,[],[f89,f74,f91])).
% 1.67/0.60  fof(f74,plain,(
% 1.67/0.60    spl3_2 <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.67/0.60  fof(f89,plain,(
% 1.67/0.60    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_2),
% 1.67/0.60    inference(resolution,[],[f76,f43])).
% 1.67/0.60  fof(f43,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f27])).
% 1.67/0.60  fof(f27,plain,(
% 1.67/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.67/0.60    inference(ennf_transformation,[],[f3])).
% 1.67/0.60  fof(f3,axiom,(
% 1.67/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.67/0.60  fof(f76,plain,(
% 1.67/0.60    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_2),
% 1.67/0.60    inference(avatar_component_clause,[],[f74])).
% 1.67/0.60  fof(f100,plain,(
% 1.67/0.60    spl3_5 | ~spl3_2),
% 1.67/0.60    inference(avatar_split_clause,[],[f88,f74,f96])).
% 1.67/0.60  fof(f88,plain,(
% 1.67/0.60    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_2),
% 1.67/0.60    inference(resolution,[],[f76,f44])).
% 1.67/0.60  fof(f85,plain,(
% 1.67/0.60    spl3_3 | ~spl3_1),
% 1.67/0.60    inference(avatar_split_clause,[],[f79,f69,f81])).
% 1.67/0.60  fof(f69,plain,(
% 1.67/0.60    spl3_1 <=> r2_hidden(sK0,sK2)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.67/0.60  fof(f79,plain,(
% 1.67/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_1),
% 1.67/0.60    inference(resolution,[],[f71,f63])).
% 1.67/0.60  fof(f63,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f42,f60,f60])).
% 1.67/0.60  fof(f42,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f26])).
% 1.67/0.60  fof(f26,plain,(
% 1.67/0.60    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.67/0.60    inference(ennf_transformation,[],[f17])).
% 1.67/0.60  fof(f17,axiom,(
% 1.67/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.67/0.60  fof(f71,plain,(
% 1.67/0.60    r2_hidden(sK0,sK2) | ~spl3_1),
% 1.67/0.60    inference(avatar_component_clause,[],[f69])).
% 1.67/0.60  fof(f77,plain,(
% 1.67/0.60    spl3_2),
% 1.67/0.60    inference(avatar_split_clause,[],[f61,f74])).
% 1.67/0.60  fof(f61,plain,(
% 1.67/0.60    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.67/0.60    inference(definition_unfolding,[],[f32,f59])).
% 1.67/0.60  fof(f32,plain,(
% 1.67/0.60    r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.67/0.60    inference(cnf_transformation,[],[f29])).
% 1.67/0.60  fof(f29,plain,(
% 1.67/0.60    r2_hidden(sK0,sK2) & r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.67/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28])).
% 1.67/0.60  fof(f28,plain,(
% 1.67/0.60    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2)) => (r2_hidden(sK0,sK2) & r1_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f23,plain,(
% 1.67/0.60    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.67/0.60    inference(ennf_transformation,[],[f21])).
% 1.67/0.60  fof(f21,negated_conjecture,(
% 1.67/0.60    ~! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.67/0.60    inference(negated_conjecture,[],[f20])).
% 1.67/0.60  fof(f20,conjecture,(
% 1.67/0.60    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.67/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.67/0.60  fof(f72,plain,(
% 1.67/0.60    spl3_1),
% 1.67/0.60    inference(avatar_split_clause,[],[f33,f69])).
% 1.67/0.60  fof(f33,plain,(
% 1.67/0.60    r2_hidden(sK0,sK2)),
% 1.67/0.60    inference(cnf_transformation,[],[f29])).
% 1.67/0.60  % SZS output end Proof for theBenchmark
% 1.67/0.60  % (10597)------------------------------
% 1.67/0.60  % (10597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (10597)Termination reason: Refutation
% 1.67/0.60  
% 1.67/0.60  % (10597)Memory used [KB]: 7036
% 1.67/0.60  % (10597)Time elapsed: 0.165 s
% 1.67/0.60  % (10597)------------------------------
% 1.67/0.60  % (10597)------------------------------
% 1.67/0.60  % (10571)Success in time 0.232 s
%------------------------------------------------------------------------------
