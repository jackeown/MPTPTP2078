%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:26 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  244 ( 839 expanded)
%              Number of leaves         :   61 ( 338 expanded)
%              Depth                    :   15
%              Number of atoms          :  514 (1364 expanded)
%              Number of equality atoms :  183 ( 761 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f97,f109,f115,f139,f184,f244,f277,f352,f485,f504,f559,f656,f657,f664,f759,f773,f786,f787,f809,f855,f867,f881,f886,f926,f934,f950,f990,f995,f1023,f1049,f1068,f1152,f1165,f1173])).

fof(f1173,plain,
    ( ~ spl5_24
    | ~ spl5_59 ),
    inference(avatar_contradiction_clause,[],[f1168])).

fof(f1168,plain,
    ( $false
    | ~ spl5_24
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f655,f73,f1166])).

fof(f1166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl5_59 ),
    inference(superposition,[],[f80,f1164])).

fof(f1164,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1162,plain,
    ( spl5_59
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f80,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f655,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl5_24
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1165,plain,
    ( spl5_59
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f1153,f1149,f241,f111,f1162])).

fof(f111,plain,
    ( spl5_4
  <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f241,plain,
    ( spl5_10
  <=> k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1149,plain,
    ( spl5_58
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f1153,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_58 ),
    inference(superposition,[],[f1151,f431])).

fof(f431,plain,
    ( ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f423,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f423,plain,
    ( ! [X7] : k5_xboole_0(X7,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X7,k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f335,f43])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f335,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f248,f119])).

fof(f119,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f116,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f116,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),X0))
    | ~ spl5_4 ),
    inference(superposition,[],[f57,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f248,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f245,f57])).

fof(f245,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))
    | ~ spl5_10 ),
    inference(superposition,[],[f57,f243])).

fof(f243,plain,
    ( k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1151,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1152,plain,
    ( spl5_58
    | ~ spl5_35
    | ~ spl5_52
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1145,f1065,f1020,f806,f1149])).

fof(f806,plain,
    ( spl5_35
  <=> k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1020,plain,
    ( spl5_52
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1065,plain,
    ( spl5_56
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1145,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_35
    | ~ spl5_52
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f1144,f1022])).

fof(f1022,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f1144,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_35
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f1143,f71])).

fof(f71,plain,(
    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f1143,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_35
    | ~ spl5_56 ),
    inference(forward_demodulation,[],[f808,f1067])).

fof(f1067,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f808,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f806])).

fof(f1068,plain,
    ( spl5_56
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f1056,f1046,f1065])).

fof(f1046,plain,
    ( spl5_55
  <=> sK0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f1056,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_55 ),
    inference(forward_demodulation,[],[f1055,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1055,plain,
    ( sK0 = k5_xboole_0(sK0,sK0)
    | ~ spl5_55 ),
    inference(forward_demodulation,[],[f1050,f1048])).

fof(f1048,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1050,plain,
    ( sK0 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK0))
    | ~ spl5_55 ),
    inference(superposition,[],[f69,f1048])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1049,plain,
    ( spl5_55
    | ~ spl5_47
    | ~ spl5_50
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f1031,f992,f987,f923,f1046])).

fof(f923,plain,
    ( spl5_47
  <=> k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f987,plain,
    ( spl5_50
  <=> sK1 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f992,plain,
    ( spl5_51
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1031,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_47
    | ~ spl5_50
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f1030,f38])).

fof(f1030,plain,
    ( k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_47
    | ~ spl5_50
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f1017,f33])).

fof(f33,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f1017,plain,
    ( k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | ~ spl5_47
    | ~ spl5_50
    | ~ spl5_51 ),
    inference(backward_demodulation,[],[f925,f1003])).

fof(f1003,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_50
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f989,f994])).

fof(f994,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f992])).

fof(f989,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f987])).

fof(f925,plain,
    ( k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(sK1))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f923])).

fof(f1023,plain,
    ( spl5_52
    | ~ spl5_50
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f1003,f992,f987,f1020])).

fof(f995,plain,
    ( spl5_51
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f985,f947,f992])).

fof(f947,plain,
    ( spl5_49
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f985,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl5_49 ),
    inference(backward_demodulation,[],[f949,f963])).

fof(f963,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f952,f38])).

fof(f952,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK1)
    | ~ spl5_49 ),
    inference(superposition,[],[f69,f949])).

fof(f949,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f947])).

fof(f990,plain,
    ( spl5_50
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f963,f947,f987])).

fof(f950,plain,
    ( spl5_49
    | ~ spl5_16
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f935,f930,f349,f947])).

fof(f349,plain,
    ( spl5_16
  <=> sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f930,plain,
    ( spl5_48
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f935,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl5_16
    | ~ spl5_48 ),
    inference(superposition,[],[f932,f377])).

fof(f377,plain,
    ( ! [X4] : k4_xboole_0(sK1,X4) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X4))
    | ~ spl5_16 ),
    inference(superposition,[],[f359,f69])).

fof(f359,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0))
    | ~ spl5_16 ),
    inference(superposition,[],[f57,f351])).

fof(f351,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f349])).

fof(f932,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f930])).

fof(f934,plain,
    ( spl5_48
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f921,f883,f930])).

fof(f883,plain,
    ( spl5_42
  <=> k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f921,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f919,f37])).

fof(f919,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))
    | ~ spl5_42 ),
    inference(superposition,[],[f76,f885])).

fof(f885,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f883])).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f67,f48])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f926,plain,
    ( spl5_47
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f887,f878,f923])).

fof(f878,plain,
    ( spl5_41
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f887,plain,
    ( k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(sK1))
    | ~ spl5_41 ),
    inference(superposition,[],[f69,f880])).

fof(f880,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k3_tarski(sK1)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f878])).

fof(f886,plain,
    ( spl5_42
    | ~ spl5_1
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f846,f771,f733,f82,f883])).

fof(f82,plain,
    ( spl5_1
  <=> k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f733,plain,
    ( spl5_30
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f771,plain,
    ( spl5_32
  <=> ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f846,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_1
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(backward_demodulation,[],[f84,f812])).

fof(f812,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f803,f38])).

fof(f803,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(backward_demodulation,[],[f735,f793])).

fof(f793,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_32 ),
    inference(resolution,[],[f772,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f772,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f771])).

fof(f735,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f733])).

fof(f84,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f881,plain,
    ( spl5_41
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f868,f864,f241,f111,f878])).

fof(f864,plain,
    ( spl5_40
  <=> k3_tarski(sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f868,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k3_tarski(sK1)
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_40 ),
    inference(superposition,[],[f866,f431])).

fof(f866,plain,
    ( k3_tarski(sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f864])).

fof(f867,plain,
    ( spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f862,f852,f864])).

fof(f852,plain,
    ( spl5_38
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f862,plain,
    ( k3_tarski(sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)))
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f861,f37])).

fof(f861,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))) = k3_tarski(sK1)
    | ~ spl5_38 ),
    inference(superposition,[],[f76,f854])).

fof(f854,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f852])).

fof(f855,plain,
    ( spl5_38
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f812,f771,f733,f852])).

fof(f809,plain,
    ( spl5_35
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f793,f771,f806])).

fof(f787,plain,
    ( sK1 != k5_xboole_0(k1_xboole_0,sK1)
    | k5_xboole_0(k1_xboole_0,sK1) != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f786,plain,
    ( spl5_33
    | ~ spl5_20
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f780,f733,f501,f783])).

fof(f783,plain,
    ( spl5_33
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f501,plain,
    ( spl5_20
  <=> k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f780,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_20
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f635,f735])).

fof(f635,plain,
    ( k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_20 ),
    inference(superposition,[],[f69,f503])).

fof(f503,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f501])).

fof(f773,plain,
    ( ~ spl5_31
    | spl5_32
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f640,f501,f771,f767])).

fof(f767,plain,
    ( spl5_31
  <=> r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f640,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
        | ~ r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl5_20 ),
    inference(superposition,[],[f78,f503])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f759,plain,
    ( spl5_30
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f681,f661,f733])).

fof(f661,plain,
    ( spl5_25
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f681,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f674,f43])).

fof(f674,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ spl5_25 ),
    inference(superposition,[],[f57,f663])).

fof(f663,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f661])).

fof(f664,plain,
    ( spl5_25
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f588,f241,f111,f93,f661])).

fof(f93,plain,
    ( spl5_2
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f588,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f577,f38])).

fof(f577,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f506,f37])).

fof(f506,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = X0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f499,f57])).

fof(f499,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = X0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f439,f478])).

fof(f478,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f468,f38])).

fof(f468,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f439,f37])).

fof(f439,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = X0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f102,f431])).

fof(f102,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl5_2 ),
    inference(superposition,[],[f57,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f657,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f656,plain,
    ( ~ spl5_23
    | spl5_24
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f571,f556,f654,f650])).

fof(f650,plain,
    ( spl5_23
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f556,plain,
    ( spl5_21
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f571,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f567,f558])).

fof(f558,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f556])).

fof(f567,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl5_21 ),
    inference(superposition,[],[f78,f558])).

fof(f559,plain,
    ( spl5_21
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f511,f241,f111,f556])).

fof(f511,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f446,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f446,plain,
    ( ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f431,f69])).

fof(f504,plain,
    ( spl5_20
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f478,f241,f111,f93,f501])).

fof(f485,plain,
    ( spl5_19
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f458,f241,f111,f482])).

fof(f482,plain,
    ( spl5_19
  <=> r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f458,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f453,f72])).

fof(f453,plain,
    ( ! [X9] : r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9)),X9)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f75,f431])).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f352,plain,
    ( spl5_16
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f342,f241,f349])).

fof(f342,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f327,f38])).

fof(f327,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_10 ),
    inference(superposition,[],[f248,f37])).

fof(f277,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f263,f136,f93,f274])).

fof(f274,plain,
    ( spl5_11
  <=> r1_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f136,plain,
    ( spl5_5
  <=> k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f263,plain,
    ( r1_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f262,f72])).

fof(f262,plain,
    ( r1_xboole_0(k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f249,f138])).

fof(f138,plain,
    ( k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f249,plain,
    ( r1_xboole_0(k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl5_2 ),
    inference(superposition,[],[f129,f37])).

fof(f129,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X4))),k5_xboole_0(k1_xboole_0,X4))
    | ~ spl5_2 ),
    inference(superposition,[],[f75,f102])).

fof(f244,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f234,f111,f105,f241])).

fof(f105,plain,
    ( spl5_3
  <=> k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f234,plain,
    ( k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f233,f38])).

fof(f233,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f225,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f225,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl5_4 ),
    inference(superposition,[],[f150,f76])).

fof(f150,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | ~ spl5_4 ),
    inference(superposition,[],[f119,f43])).

fof(f184,plain,
    ( spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f162,f93,f181])).

fof(f181,plain,
    ( spl5_7
  <=> k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f162,plain,
    ( k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f121,f69])).

fof(f121,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl5_2 ),
    inference(superposition,[],[f102,f43])).

fof(f139,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f130,f93,f136])).

fof(f130,plain,
    ( k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f120,f38])).

fof(f120,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f102,f37])).

fof(f115,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f101,f93,f111])).

fof(f101,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl5_2 ),
    inference(superposition,[],[f57,f95])).

fof(f109,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f100,f93,f105])).

fof(f100,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f76,f95])).

fof(f97,plain,
    ( spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f91,f82,f93])).

fof(f91,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f90,f43])).

fof(f90,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f87,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f48,f48])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f87,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_1 ),
    inference(superposition,[],[f76,f84])).

fof(f85,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f70,f82])).

fof(f70,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f32,f67,f68])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (4585)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (4583)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (4601)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (4593)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (4592)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.53  % (4602)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (4581)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (4580)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (4594)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (4582)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (4602)Refutation not found, incomplete strategy% (4602)------------------------------
% 1.29/0.53  % (4602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (4602)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (4602)Memory used [KB]: 1663
% 1.29/0.53  % (4602)Time elapsed: 0.079 s
% 1.29/0.53  % (4602)------------------------------
% 1.29/0.53  % (4602)------------------------------
% 1.29/0.54  % (4584)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (4594)Refutation not found, incomplete strategy% (4594)------------------------------
% 1.29/0.54  % (4594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (4594)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (4594)Memory used [KB]: 6140
% 1.29/0.54  % (4594)Time elapsed: 0.004 s
% 1.29/0.54  % (4594)------------------------------
% 1.29/0.54  % (4594)------------------------------
% 1.29/0.54  % (4586)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (4597)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.54  % (4603)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.54  % (4607)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.54  % (4606)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.54  % (4605)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (4591)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (4598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (4608)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (4589)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (4589)Refutation not found, incomplete strategy% (4589)------------------------------
% 1.43/0.55  % (4589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (4589)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (4589)Memory used [KB]: 10618
% 1.43/0.55  % (4589)Time elapsed: 0.139 s
% 1.43/0.55  % (4589)------------------------------
% 1.43/0.55  % (4589)------------------------------
% 1.43/0.55  % (4596)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (4596)Refutation not found, incomplete strategy% (4596)------------------------------
% 1.43/0.55  % (4596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (4596)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (4596)Memory used [KB]: 10618
% 1.43/0.55  % (4596)Time elapsed: 0.138 s
% 1.43/0.55  % (4596)------------------------------
% 1.43/0.55  % (4596)------------------------------
% 1.43/0.55  % (4599)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.56  % (4600)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (4590)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (4599)Refutation not found, incomplete strategy% (4599)------------------------------
% 1.43/0.56  % (4599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (4599)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (4599)Memory used [KB]: 10746
% 1.43/0.56  % (4599)Time elapsed: 0.150 s
% 1.43/0.56  % (4599)------------------------------
% 1.43/0.56  % (4599)------------------------------
% 1.43/0.56  % (4579)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.43/0.56  % (4588)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.57  % (4595)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.57  % (4601)Refutation found. Thanks to Tanya!
% 1.43/0.57  % SZS status Theorem for theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f1177,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(avatar_sat_refutation,[],[f85,f97,f109,f115,f139,f184,f244,f277,f352,f485,f504,f559,f656,f657,f664,f759,f773,f786,f787,f809,f855,f867,f881,f886,f926,f934,f950,f990,f995,f1023,f1049,f1068,f1152,f1165,f1173])).
% 1.43/0.57  fof(f1173,plain,(
% 1.43/0.57    ~spl5_24 | ~spl5_59),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f1168])).
% 1.43/0.57  fof(f1168,plain,(
% 1.43/0.57    $false | (~spl5_24 | ~spl5_59)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f655,f73,f1166])).
% 1.43/0.57  fof(f1166,plain,(
% 1.43/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | r2_hidden(X0,k1_xboole_0)) ) | ~spl5_59),
% 1.43/0.57    inference(superposition,[],[f80,f1164])).
% 1.43/0.57  fof(f1164,plain,(
% 1.43/0.57    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | ~spl5_59),
% 1.43/0.57    inference(avatar_component_clause,[],[f1162])).
% 1.43/0.57  fof(f1162,plain,(
% 1.43/0.57    spl5_59 <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 1.43/0.57  fof(f80,plain,(
% 1.43/0.57    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.43/0.57    inference(equality_resolution,[],[f52])).
% 1.43/0.57  fof(f52,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.43/0.57    inference(cnf_transformation,[],[f22])).
% 1.43/0.57  fof(f22,axiom,(
% 1.43/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.43/0.57  fof(f73,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f41,f48])).
% 1.43/0.57  fof(f48,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f9])).
% 1.43/0.57  fof(f9,axiom,(
% 1.43/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.43/0.57  fof(f41,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f7])).
% 1.43/0.57  fof(f7,axiom,(
% 1.43/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.43/0.57  fof(f655,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_24),
% 1.43/0.57    inference(avatar_component_clause,[],[f654])).
% 1.43/0.57  fof(f654,plain,(
% 1.43/0.57    spl5_24 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.43/0.57  fof(f1165,plain,(
% 1.43/0.57    spl5_59 | ~spl5_4 | ~spl5_10 | ~spl5_58),
% 1.43/0.57    inference(avatar_split_clause,[],[f1153,f1149,f241,f111,f1162])).
% 1.43/0.57  fof(f111,plain,(
% 1.43/0.57    spl5_4 <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.43/0.57  fof(f241,plain,(
% 1.43/0.57    spl5_10 <=> k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.43/0.57  fof(f1149,plain,(
% 1.43/0.57    spl5_58 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 1.43/0.57  fof(f1153,plain,(
% 1.43/0.57    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | (~spl5_4 | ~spl5_10 | ~spl5_58)),
% 1.43/0.57    inference(superposition,[],[f1151,f431])).
% 1.43/0.57  fof(f431,plain,(
% 1.43/0.57    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = X7) ) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(forward_demodulation,[],[f423,f38])).
% 1.43/0.57  fof(f38,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.57    inference(cnf_transformation,[],[f10])).
% 1.43/0.57  fof(f10,axiom,(
% 1.43/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.43/0.57  fof(f423,plain,(
% 1.43/0.57    ( ! [X7] : (k5_xboole_0(X7,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X7,k1_xboole_0))) ) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f335,f43])).
% 1.43/0.57  fof(f43,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f2])).
% 1.43/0.57  fof(f2,axiom,(
% 1.43/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.43/0.57  fof(f335,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f248,f119])).
% 1.43/0.57  fof(f119,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)))) ) | ~spl5_4),
% 1.43/0.57    inference(forward_demodulation,[],[f116,f57])).
% 1.43/0.57  fof(f57,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f12])).
% 1.43/0.57  fof(f12,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.43/0.57  fof(f116,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),X0))) ) | ~spl5_4),
% 1.43/0.57    inference(superposition,[],[f57,f113])).
% 1.43/0.57  fof(f113,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl5_4),
% 1.43/0.57    inference(avatar_component_clause,[],[f111])).
% 1.43/0.57  fof(f248,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) ) | ~spl5_10),
% 1.43/0.57    inference(forward_demodulation,[],[f245,f57])).
% 1.43/0.57  fof(f245,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) ) | ~spl5_10),
% 1.43/0.57    inference(superposition,[],[f57,f243])).
% 1.43/0.57  fof(f243,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_10),
% 1.43/0.57    inference(avatar_component_clause,[],[f241])).
% 1.43/0.57  fof(f1151,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl5_58),
% 1.43/0.57    inference(avatar_component_clause,[],[f1149])).
% 1.43/0.57  fof(f1152,plain,(
% 1.43/0.57    spl5_58 | ~spl5_35 | ~spl5_52 | ~spl5_56),
% 1.43/0.57    inference(avatar_split_clause,[],[f1145,f1065,f1020,f806,f1149])).
% 1.43/0.57  fof(f806,plain,(
% 1.43/0.57    spl5_35 <=> k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.43/0.57  fof(f1020,plain,(
% 1.43/0.57    spl5_52 <=> k1_xboole_0 = sK1),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.43/0.57  fof(f1065,plain,(
% 1.43/0.57    spl5_56 <=> k1_xboole_0 = sK0),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 1.43/0.57  fof(f1145,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_35 | ~spl5_52 | ~spl5_56)),
% 1.43/0.57    inference(forward_demodulation,[],[f1144,f1022])).
% 1.43/0.57  fof(f1022,plain,(
% 1.43/0.57    k1_xboole_0 = sK1 | ~spl5_52),
% 1.43/0.57    inference(avatar_component_clause,[],[f1020])).
% 1.43/0.57  fof(f1144,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl5_35 | ~spl5_56)),
% 1.43/0.57    inference(forward_demodulation,[],[f1143,f71])).
% 1.43/0.57  fof(f71,plain,(
% 1.43/0.57    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.43/0.57    inference(definition_unfolding,[],[f34,f68])).
% 1.43/0.57  fof(f68,plain,(
% 1.43/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f39,f66])).
% 1.43/0.57  fof(f66,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f46,f65])).
% 1.43/0.57  fof(f65,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f56,f64])).
% 1.43/0.57  fof(f64,plain,(
% 1.43/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f58,f63])).
% 1.43/0.57  fof(f63,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f59,f62])).
% 1.43/0.57  fof(f62,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f60,f61])).
% 1.43/0.57  fof(f61,plain,(
% 1.43/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f21])).
% 1.43/0.57  fof(f21,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.43/0.57  fof(f60,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f20])).
% 1.43/0.57  fof(f20,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.43/0.57  fof(f59,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f19,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.43/0.57  fof(f58,plain,(
% 1.43/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f18])).
% 1.43/0.57  fof(f18,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.43/0.57  fof(f56,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  fof(f17,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.57  fof(f46,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f16])).
% 1.43/0.57  fof(f16,axiom,(
% 1.43/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.57  fof(f39,plain,(
% 1.43/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f15,axiom,(
% 1.43/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.43/0.57  fof(f34,plain,(
% 1.43/0.57    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.43/0.57    inference(cnf_transformation,[],[f24])).
% 1.43/0.57  fof(f24,axiom,(
% 1.43/0.57    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.43/0.57  fof(f1143,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl5_35 | ~spl5_56)),
% 1.43/0.57    inference(forward_demodulation,[],[f808,f1067])).
% 1.43/0.57  fof(f1067,plain,(
% 1.43/0.57    k1_xboole_0 = sK0 | ~spl5_56),
% 1.43/0.57    inference(avatar_component_clause,[],[f1065])).
% 1.43/0.57  fof(f808,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_35),
% 1.43/0.57    inference(avatar_component_clause,[],[f806])).
% 1.43/0.57  fof(f1068,plain,(
% 1.43/0.57    spl5_56 | ~spl5_55),
% 1.43/0.57    inference(avatar_split_clause,[],[f1056,f1046,f1065])).
% 1.43/0.57  fof(f1046,plain,(
% 1.43/0.57    spl5_55 <=> sK0 = k4_xboole_0(sK0,sK0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.43/0.57  fof(f1056,plain,(
% 1.43/0.57    k1_xboole_0 = sK0 | ~spl5_55),
% 1.43/0.57    inference(forward_demodulation,[],[f1055,f37])).
% 1.43/0.57  fof(f37,plain,(
% 1.43/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f13])).
% 1.43/0.57  fof(f13,axiom,(
% 1.43/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.43/0.57  fof(f1055,plain,(
% 1.43/0.57    sK0 = k5_xboole_0(sK0,sK0) | ~spl5_55),
% 1.43/0.57    inference(forward_demodulation,[],[f1050,f1048])).
% 1.43/0.57  fof(f1048,plain,(
% 1.43/0.57    sK0 = k4_xboole_0(sK0,sK0) | ~spl5_55),
% 1.43/0.57    inference(avatar_component_clause,[],[f1046])).
% 1.43/0.57  fof(f1050,plain,(
% 1.43/0.57    sK0 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) | ~spl5_55),
% 1.43/0.57    inference(superposition,[],[f69,f1048])).
% 1.43/0.57  fof(f69,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f47,f48])).
% 1.43/0.57  fof(f47,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f6])).
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.57  fof(f1049,plain,(
% 1.43/0.57    spl5_55 | ~spl5_47 | ~spl5_50 | ~spl5_51),
% 1.43/0.57    inference(avatar_split_clause,[],[f1031,f992,f987,f923,f1046])).
% 1.43/0.57  fof(f923,plain,(
% 1.43/0.57    spl5_47 <=> k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 1.43/0.57  fof(f987,plain,(
% 1.43/0.57    spl5_50 <=> sK1 = k4_xboole_0(sK1,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.43/0.57  fof(f992,plain,(
% 1.43/0.57    spl5_51 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.43/0.57  fof(f1031,plain,(
% 1.43/0.57    sK0 = k4_xboole_0(sK0,sK0) | (~spl5_47 | ~spl5_50 | ~spl5_51)),
% 1.43/0.57    inference(forward_demodulation,[],[f1030,f38])).
% 1.43/0.57  fof(f1030,plain,(
% 1.43/0.57    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k1_xboole_0) | (~spl5_47 | ~spl5_50 | ~spl5_51)),
% 1.43/0.57    inference(forward_demodulation,[],[f1017,f33])).
% 1.43/0.57  fof(f33,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.43/0.57    inference(cnf_transformation,[],[f25])).
% 1.43/0.57  fof(f25,axiom,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.43/0.57  fof(f1017,plain,(
% 1.43/0.57    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(k1_xboole_0)) | (~spl5_47 | ~spl5_50 | ~spl5_51)),
% 1.43/0.57    inference(backward_demodulation,[],[f925,f1003])).
% 1.43/0.57  fof(f1003,plain,(
% 1.43/0.57    k1_xboole_0 = sK1 | (~spl5_50 | ~spl5_51)),
% 1.43/0.57    inference(forward_demodulation,[],[f989,f994])).
% 1.43/0.57  fof(f994,plain,(
% 1.43/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl5_51),
% 1.43/0.57    inference(avatar_component_clause,[],[f992])).
% 1.43/0.57  fof(f989,plain,(
% 1.43/0.57    sK1 = k4_xboole_0(sK1,sK1) | ~spl5_50),
% 1.43/0.57    inference(avatar_component_clause,[],[f987])).
% 1.43/0.57  fof(f925,plain,(
% 1.43/0.57    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(sK1)) | ~spl5_47),
% 1.43/0.57    inference(avatar_component_clause,[],[f923])).
% 1.43/0.57  fof(f1023,plain,(
% 1.43/0.57    spl5_52 | ~spl5_50 | ~spl5_51),
% 1.43/0.57    inference(avatar_split_clause,[],[f1003,f992,f987,f1020])).
% 1.43/0.57  fof(f995,plain,(
% 1.43/0.57    spl5_51 | ~spl5_49),
% 1.43/0.57    inference(avatar_split_clause,[],[f985,f947,f992])).
% 1.43/0.57  fof(f947,plain,(
% 1.43/0.57    spl5_49 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.43/0.57  fof(f985,plain,(
% 1.43/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl5_49),
% 1.43/0.57    inference(backward_demodulation,[],[f949,f963])).
% 1.43/0.57  fof(f963,plain,(
% 1.43/0.57    sK1 = k4_xboole_0(sK1,sK1) | ~spl5_49),
% 1.43/0.57    inference(forward_demodulation,[],[f952,f38])).
% 1.43/0.57  fof(f952,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK1) | ~spl5_49),
% 1.43/0.57    inference(superposition,[],[f69,f949])).
% 1.43/0.57  fof(f949,plain,(
% 1.43/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | ~spl5_49),
% 1.43/0.57    inference(avatar_component_clause,[],[f947])).
% 1.43/0.57  fof(f990,plain,(
% 1.43/0.57    spl5_50 | ~spl5_49),
% 1.43/0.57    inference(avatar_split_clause,[],[f963,f947,f987])).
% 1.43/0.57  fof(f950,plain,(
% 1.43/0.57    spl5_49 | ~spl5_16 | ~spl5_48),
% 1.43/0.57    inference(avatar_split_clause,[],[f935,f930,f349,f947])).
% 1.43/0.57  fof(f349,plain,(
% 1.43/0.57    spl5_16 <=> sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.43/0.57  fof(f930,plain,(
% 1.43/0.57    spl5_48 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.43/0.57  fof(f935,plain,(
% 1.43/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | (~spl5_16 | ~spl5_48)),
% 1.43/0.57    inference(superposition,[],[f932,f377])).
% 1.43/0.57  fof(f377,plain,(
% 1.43/0.57    ( ! [X4] : (k4_xboole_0(sK1,X4) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X4))) ) | ~spl5_16),
% 1.43/0.57    inference(superposition,[],[f359,f69])).
% 1.43/0.57  fof(f359,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0))) ) | ~spl5_16),
% 1.43/0.57    inference(superposition,[],[f57,f351])).
% 1.43/0.57  fof(f351,plain,(
% 1.43/0.57    sK1 = k5_xboole_0(k1_xboole_0,sK1) | ~spl5_16),
% 1.43/0.57    inference(avatar_component_clause,[],[f349])).
% 1.43/0.57  fof(f932,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) | ~spl5_48),
% 1.43/0.57    inference(avatar_component_clause,[],[f930])).
% 1.43/0.57  fof(f934,plain,(
% 1.43/0.57    spl5_48 | ~spl5_42),
% 1.43/0.57    inference(avatar_split_clause,[],[f921,f883,f930])).
% 1.43/0.57  fof(f883,plain,(
% 1.43/0.57    spl5_42 <=> k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.43/0.57  fof(f921,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) | ~spl5_42),
% 1.43/0.57    inference(forward_demodulation,[],[f919,f37])).
% 1.43/0.57  fof(f919,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) | ~spl5_42),
% 1.43/0.57    inference(superposition,[],[f76,f885])).
% 1.43/0.57  fof(f885,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_42),
% 1.43/0.57    inference(avatar_component_clause,[],[f883])).
% 1.43/0.57  fof(f76,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f49,f67,f48])).
% 1.43/0.57  fof(f67,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f45,f66])).
% 1.43/0.57  fof(f45,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f23])).
% 1.43/0.57  fof(f23,axiom,(
% 1.43/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.43/0.57  fof(f49,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f14])).
% 1.43/0.57  fof(f14,axiom,(
% 1.43/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.43/0.57  fof(f926,plain,(
% 1.43/0.57    spl5_47 | ~spl5_41),
% 1.43/0.57    inference(avatar_split_clause,[],[f887,f878,f923])).
% 1.43/0.57  fof(f878,plain,(
% 1.43/0.57    spl5_41 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k3_tarski(sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.43/0.57  fof(f887,plain,(
% 1.43/0.57    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_tarski(sK1)) | ~spl5_41),
% 1.43/0.57    inference(superposition,[],[f69,f880])).
% 1.43/0.57  fof(f880,plain,(
% 1.43/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k3_tarski(sK1) | ~spl5_41),
% 1.43/0.57    inference(avatar_component_clause,[],[f878])).
% 1.43/0.57  fof(f886,plain,(
% 1.43/0.57    spl5_42 | ~spl5_1 | ~spl5_30 | ~spl5_32),
% 1.43/0.57    inference(avatar_split_clause,[],[f846,f771,f733,f82,f883])).
% 1.43/0.57  fof(f82,plain,(
% 1.43/0.57    spl5_1 <=> k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.43/0.57  fof(f733,plain,(
% 1.43/0.57    spl5_30 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.43/0.57  fof(f771,plain,(
% 1.43/0.57    spl5_32 <=> ! [X0] : ~r2_hidden(X0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.43/0.57  fof(f846,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | (~spl5_1 | ~spl5_30 | ~spl5_32)),
% 1.43/0.57    inference(backward_demodulation,[],[f84,f812])).
% 1.43/0.57  fof(f812,plain,(
% 1.43/0.57    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl5_30 | ~spl5_32)),
% 1.43/0.57    inference(forward_demodulation,[],[f803,f38])).
% 1.43/0.57  fof(f803,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k1_xboole_0) | (~spl5_30 | ~spl5_32)),
% 1.43/0.57    inference(backward_demodulation,[],[f735,f793])).
% 1.43/0.57  fof(f793,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_32),
% 1.43/0.57    inference(resolution,[],[f772,f40])).
% 1.43/0.57  fof(f40,plain,(
% 1.43/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.43/0.57    inference(cnf_transformation,[],[f30])).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.43/0.57    inference(ennf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.43/0.57  fof(f772,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl5_32),
% 1.43/0.57    inference(avatar_component_clause,[],[f771])).
% 1.43/0.57  fof(f735,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_30),
% 1.43/0.57    inference(avatar_component_clause,[],[f733])).
% 1.43/0.57  fof(f84,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | ~spl5_1),
% 1.43/0.57    inference(avatar_component_clause,[],[f82])).
% 1.43/0.57  fof(f881,plain,(
% 1.43/0.57    spl5_41 | ~spl5_4 | ~spl5_10 | ~spl5_40),
% 1.43/0.57    inference(avatar_split_clause,[],[f868,f864,f241,f111,f878])).
% 1.43/0.57  fof(f864,plain,(
% 1.43/0.57    spl5_40 <=> k3_tarski(sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.43/0.57  fof(f868,plain,(
% 1.43/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k3_tarski(sK1) | (~spl5_4 | ~spl5_10 | ~spl5_40)),
% 1.43/0.57    inference(superposition,[],[f866,f431])).
% 1.43/0.57  fof(f866,plain,(
% 1.43/0.57    k3_tarski(sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))) | ~spl5_40),
% 1.43/0.57    inference(avatar_component_clause,[],[f864])).
% 1.43/0.57  fof(f867,plain,(
% 1.43/0.57    spl5_40 | ~spl5_38),
% 1.43/0.57    inference(avatar_split_clause,[],[f862,f852,f864])).
% 1.43/0.57  fof(f852,plain,(
% 1.43/0.57    spl5_38 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.43/0.57  fof(f862,plain,(
% 1.43/0.57    k3_tarski(sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))) | ~spl5_38),
% 1.43/0.57    inference(forward_demodulation,[],[f861,f37])).
% 1.43/0.57  fof(f861,plain,(
% 1.43/0.57    k5_xboole_0(k5_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))) = k3_tarski(sK1) | ~spl5_38),
% 1.43/0.57    inference(superposition,[],[f76,f854])).
% 1.43/0.57  fof(f854,plain,(
% 1.43/0.57    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_38),
% 1.43/0.57    inference(avatar_component_clause,[],[f852])).
% 1.43/0.57  fof(f855,plain,(
% 1.43/0.57    spl5_38 | ~spl5_30 | ~spl5_32),
% 1.43/0.57    inference(avatar_split_clause,[],[f812,f771,f733,f852])).
% 1.43/0.57  fof(f809,plain,(
% 1.43/0.57    spl5_35 | ~spl5_32),
% 1.43/0.57    inference(avatar_split_clause,[],[f793,f771,f806])).
% 1.43/0.57  fof(f787,plain,(
% 1.43/0.57    sK1 != k5_xboole_0(k1_xboole_0,sK1) | k5_xboole_0(k1_xboole_0,sK1) != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r1_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.43/0.57  fof(f786,plain,(
% 1.43/0.57    spl5_33 | ~spl5_20 | ~spl5_30),
% 1.43/0.57    inference(avatar_split_clause,[],[f780,f733,f501,f783])).
% 1.43/0.57  fof(f783,plain,(
% 1.43/0.57    spl5_33 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.43/0.57  fof(f501,plain,(
% 1.43/0.57    spl5_20 <=> k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.43/0.57  fof(f780,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl5_20 | ~spl5_30)),
% 1.43/0.57    inference(forward_demodulation,[],[f635,f735])).
% 1.43/0.57  fof(f635,plain,(
% 1.43/0.57    k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_20),
% 1.43/0.57    inference(superposition,[],[f69,f503])).
% 1.43/0.57  fof(f503,plain,(
% 1.43/0.57    k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_20),
% 1.43/0.57    inference(avatar_component_clause,[],[f501])).
% 1.43/0.57  fof(f773,plain,(
% 1.43/0.57    ~spl5_31 | spl5_32 | ~spl5_20),
% 1.43/0.57    inference(avatar_split_clause,[],[f640,f501,f771,f767])).
% 1.43/0.57  fof(f767,plain,(
% 1.43/0.57    spl5_31 <=> r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.43/0.57  fof(f640,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ) | ~spl5_20),
% 1.43/0.57    inference(superposition,[],[f78,f503])).
% 1.43/0.57  fof(f78,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f50,f48])).
% 1.43/0.57  fof(f50,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f31])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.43/0.57    inference(ennf_transformation,[],[f28])).
% 1.43/0.57  fof(f28,plain,(
% 1.43/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.43/0.57    inference(rectify,[],[f3])).
% 1.43/0.57  fof(f3,axiom,(
% 1.43/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.43/0.57  fof(f759,plain,(
% 1.43/0.57    spl5_30 | ~spl5_25),
% 1.43/0.57    inference(avatar_split_clause,[],[f681,f661,f733])).
% 1.43/0.57  fof(f661,plain,(
% 1.43/0.57    spl5_25 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.43/0.57  fof(f681,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_25),
% 1.43/0.57    inference(forward_demodulation,[],[f674,f43])).
% 1.43/0.57  fof(f674,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | ~spl5_25),
% 1.43/0.57    inference(superposition,[],[f57,f663])).
% 1.43/0.57  fof(f663,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | ~spl5_25),
% 1.43/0.57    inference(avatar_component_clause,[],[f661])).
% 1.43/0.57  fof(f664,plain,(
% 1.43/0.57    spl5_25 | ~spl5_2 | ~spl5_4 | ~spl5_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f588,f241,f111,f93,f661])).
% 1.43/0.57  fof(f93,plain,(
% 1.43/0.57    spl5_2 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.43/0.57  fof(f588,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(forward_demodulation,[],[f577,f38])).
% 1.43/0.57  fof(f577,plain,(
% 1.43/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0)) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f506,f37])).
% 1.43/0.57  fof(f506,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = X0) ) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(forward_demodulation,[],[f499,f57])).
% 1.43/0.57  fof(f499,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = X0) ) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(backward_demodulation,[],[f439,f478])).
% 1.43/0.57  fof(f478,plain,(
% 1.43/0.57    k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(forward_demodulation,[],[f468,f38])).
% 1.43/0.57  fof(f468,plain,(
% 1.43/0.57    k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f439,f37])).
% 1.43/0.57  fof(f439,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = X0) ) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(backward_demodulation,[],[f102,f431])).
% 1.43/0.57  fof(f102,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k1_xboole_0,X0)) ) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f57,f95])).
% 1.43/0.57  fof(f95,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_2),
% 1.43/0.57    inference(avatar_component_clause,[],[f93])).
% 1.43/0.57  fof(f657,plain,(
% 1.43/0.57    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.43/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.43/0.57  fof(f656,plain,(
% 1.43/0.57    ~spl5_23 | spl5_24 | ~spl5_21),
% 1.43/0.57    inference(avatar_split_clause,[],[f571,f556,f654,f650])).
% 1.43/0.57  fof(f650,plain,(
% 1.43/0.57    spl5_23 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.43/0.57  fof(f556,plain,(
% 1.43/0.57    spl5_21 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.43/0.57  fof(f571,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl5_21),
% 1.43/0.57    inference(forward_demodulation,[],[f567,f558])).
% 1.43/0.57  fof(f558,plain,(
% 1.43/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_21),
% 1.43/0.57    inference(avatar_component_clause,[],[f556])).
% 1.43/0.57  fof(f567,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl5_21),
% 1.43/0.57    inference(superposition,[],[f78,f558])).
% 1.43/0.57  fof(f559,plain,(
% 1.43/0.57    spl5_21 | ~spl5_4 | ~spl5_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f511,f241,f111,f556])).
% 1.43/0.57  fof(f511,plain,(
% 1.43/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f446,f72])).
% 1.43/0.57  fof(f72,plain,(
% 1.43/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f36,f48])).
% 1.43/0.57  fof(f36,plain,(
% 1.43/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f8])).
% 1.43/0.57  fof(f8,axiom,(
% 1.43/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.43/0.57  fof(f446,plain,(
% 1.43/0.57    ( ! [X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9))) ) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f431,f69])).
% 1.43/0.57  fof(f504,plain,(
% 1.43/0.57    spl5_20 | ~spl5_2 | ~spl5_4 | ~spl5_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f478,f241,f111,f93,f501])).
% 1.43/0.57  fof(f485,plain,(
% 1.43/0.57    spl5_19 | ~spl5_4 | ~spl5_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f458,f241,f111,f482])).
% 1.43/0.57  fof(f482,plain,(
% 1.43/0.57    spl5_19 <=> r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.43/0.57  fof(f458,plain,(
% 1.43/0.57    r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f453,f72])).
% 1.43/0.57  fof(f453,plain,(
% 1.43/0.57    ( ! [X9] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9)),X9)) ) | (~spl5_4 | ~spl5_10)),
% 1.43/0.57    inference(superposition,[],[f75,f431])).
% 1.43/0.57  fof(f75,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f44,f48])).
% 1.43/0.57  fof(f44,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f5])).
% 1.43/0.57  fof(f5,axiom,(
% 1.43/0.57    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.43/0.57  fof(f352,plain,(
% 1.43/0.57    spl5_16 | ~spl5_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f342,f241,f349])).
% 1.43/0.57  fof(f342,plain,(
% 1.43/0.57    sK1 = k5_xboole_0(k1_xboole_0,sK1) | ~spl5_10),
% 1.43/0.57    inference(forward_demodulation,[],[f327,f38])).
% 1.43/0.57  fof(f327,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k1_xboole_0)) | ~spl5_10),
% 1.43/0.57    inference(superposition,[],[f248,f37])).
% 1.43/0.57  fof(f277,plain,(
% 1.43/0.57    spl5_11 | ~spl5_2 | ~spl5_5),
% 1.43/0.57    inference(avatar_split_clause,[],[f263,f136,f93,f274])).
% 1.43/0.57  fof(f274,plain,(
% 1.43/0.57    spl5_11 <=> r1_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.43/0.57  fof(f136,plain,(
% 1.43/0.57    spl5_5 <=> k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.43/0.57  fof(f263,plain,(
% 1.43/0.57    r1_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl5_2 | ~spl5_5)),
% 1.43/0.57    inference(forward_demodulation,[],[f262,f72])).
% 1.43/0.57  fof(f262,plain,(
% 1.43/0.57    r1_xboole_0(k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl5_2 | ~spl5_5)),
% 1.43/0.57    inference(forward_demodulation,[],[f249,f138])).
% 1.43/0.57  fof(f138,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_5),
% 1.43/0.57    inference(avatar_component_clause,[],[f136])).
% 1.43/0.57  fof(f249,plain,(
% 1.43/0.57    r1_xboole_0(k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f129,f37])).
% 1.43/0.57  fof(f129,plain,(
% 1.43/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X4))),k5_xboole_0(k1_xboole_0,X4))) ) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f75,f102])).
% 1.43/0.57  fof(f244,plain,(
% 1.43/0.57    spl5_10 | ~spl5_3 | ~spl5_4),
% 1.43/0.57    inference(avatar_split_clause,[],[f234,f111,f105,f241])).
% 1.43/0.57  fof(f105,plain,(
% 1.43/0.57    spl5_3 <=> k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.43/0.57  fof(f234,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl5_3 | ~spl5_4)),
% 1.43/0.57    inference(forward_demodulation,[],[f233,f38])).
% 1.43/0.57  fof(f233,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl5_3 | ~spl5_4)),
% 1.43/0.57    inference(forward_demodulation,[],[f225,f107])).
% 1.43/0.57  fof(f107,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_3),
% 1.43/0.57    inference(avatar_component_clause,[],[f105])).
% 1.43/0.57  fof(f225,plain,(
% 1.43/0.57    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl5_4),
% 1.43/0.57    inference(superposition,[],[f150,f76])).
% 1.43/0.57  fof(f150,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ) | ~spl5_4),
% 1.43/0.57    inference(superposition,[],[f119,f43])).
% 1.43/0.57  fof(f184,plain,(
% 1.43/0.57    spl5_7 | ~spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f162,f93,f181])).
% 1.43/0.57  fof(f181,plain,(
% 1.43/0.57    spl5_7 <=> k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.43/0.57  fof(f162,plain,(
% 1.43/0.57    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f121,f69])).
% 1.43/0.57  fof(f121,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f102,f43])).
% 1.43/0.57  fof(f139,plain,(
% 1.43/0.57    spl5_5 | ~spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f130,f93,f136])).
% 1.43/0.57  fof(f130,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_2),
% 1.43/0.57    inference(forward_demodulation,[],[f120,f38])).
% 1.43/0.57  fof(f120,plain,(
% 1.43/0.57    k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f102,f37])).
% 1.43/0.57  fof(f115,plain,(
% 1.43/0.57    spl5_4 | ~spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f101,f93,f111])).
% 1.43/0.57  fof(f101,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f57,f95])).
% 1.43/0.57  fof(f109,plain,(
% 1.43/0.57    spl5_3 | ~spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f100,f93,f105])).
% 1.43/0.57  fof(f100,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_2),
% 1.43/0.57    inference(superposition,[],[f76,f95])).
% 1.43/0.57  fof(f97,plain,(
% 1.43/0.57    spl5_2 | ~spl5_1),
% 1.43/0.57    inference(avatar_split_clause,[],[f91,f82,f93])).
% 1.43/0.57  fof(f91,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_1),
% 1.43/0.57    inference(forward_demodulation,[],[f90,f43])).
% 1.43/0.57  fof(f90,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_1),
% 1.43/0.57    inference(forward_demodulation,[],[f87,f74])).
% 1.43/0.57  fof(f74,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f42,f48,f48])).
% 1.43/0.57  fof(f42,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f1])).
% 1.43/0.57  fof(f1,axiom,(
% 1.43/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.57  fof(f87,plain,(
% 1.43/0.57    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | ~spl5_1),
% 1.43/0.57    inference(superposition,[],[f76,f84])).
% 1.43/0.57  fof(f85,plain,(
% 1.43/0.57    spl5_1),
% 1.43/0.57    inference(avatar_split_clause,[],[f70,f82])).
% 1.43/0.57  fof(f70,plain,(
% 1.43/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.43/0.57    inference(definition_unfolding,[],[f32,f67,f68])).
% 1.43/0.57  fof(f32,plain,(
% 1.43/0.57    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.43/0.57    inference(cnf_transformation,[],[f29])).
% 1.43/0.57  fof(f29,plain,(
% 1.43/0.57    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.43/0.57    inference(ennf_transformation,[],[f27])).
% 1.43/0.57  fof(f27,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.43/0.57    inference(negated_conjecture,[],[f26])).
% 1.43/0.57  fof(f26,conjecture,(
% 1.43/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (4601)------------------------------
% 1.43/0.57  % (4601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (4601)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (4601)Memory used [KB]: 11513
% 1.43/0.57  % (4601)Time elapsed: 0.159 s
% 1.43/0.57  % (4601)------------------------------
% 1.43/0.57  % (4601)------------------------------
% 1.43/0.57  % (4604)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.57  % (4578)Success in time 0.208 s
%------------------------------------------------------------------------------
