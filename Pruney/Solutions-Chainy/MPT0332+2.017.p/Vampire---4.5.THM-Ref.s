%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:11 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 404 expanded)
%              Number of leaves         :   27 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 509 expanded)
%              Number of equality atoms :   88 ( 389 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1509,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f153,f159,f180,f291,f335,f1407,f1503,f1508])).

fof(f1508,plain,
    ( k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK2 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1503,plain,
    ( spl3_40
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f1476,f1404,f1500])).

fof(f1500,plain,
    ( spl3_40
  <=> k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f1404,plain,
    ( spl3_32
  <=> k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1476,plain,
    ( k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_32 ),
    inference(superposition,[],[f566,f1406])).

fof(f1406,plain,
    ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f1404])).

fof(f566,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X6,k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f545,f90])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f63,f79])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f72,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f63,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f545,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k2_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(X6,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f89,f218])).

fof(f218,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f206,f25])).

fof(f206,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f90,f66])).

fof(f66,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f32,f24])).

fof(f89,plain,(
    ! [X6,X4,X5] : k5_xboole_0(k5_xboole_0(X4,k2_xboole_0(X4,X5)),k5_xboole_0(k2_xboole_0(X4,k2_xboole_0(X4,X5)),X6)) = k5_xboole_0(X4,X6) ),
    inference(superposition,[],[f32,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1407,plain,
    ( spl3_32
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1402,f288,f1404])).

fof(f288,plain,
    ( spl3_14
  <=> k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1402,plain,
    ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f290,f235])).

fof(f235,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f90,f218])).

fof(f290,plain,
    ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f288])).

fof(f335,plain,
    ( spl3_19
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f317,f177,f332])).

fof(f332,plain,
    ( spl3_19
  <=> k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f177,plain,
    ( spl3_7
  <=> sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f317,plain,
    ( k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_7 ),
    inference(superposition,[],[f229,f179])).

fof(f179,plain,
    ( sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f177])).

fof(f229,plain,(
    ! [X6,X7] : k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6 ),
    inference(superposition,[],[f218,f218])).

fof(f291,plain,
    ( spl3_14
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f282,f177,f288])).

fof(f282,plain,
    ( k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f116,f179])).

fof(f116,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f93,f90])).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0))))) ),
    inference(forward_demodulation,[],[f44,f32])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f180,plain,
    ( spl3_7
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f164,f59,f54,f177])).

fof(f54,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f164,plain,
    ( sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f61,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ) ),
    inference(forward_demodulation,[],[f160,f90])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(forward_demodulation,[],[f47,f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f33,f38,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f61,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f56,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f159,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f154,f150,f156])).

fof(f156,plain,
    ( spl3_5
  <=> sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f150,plain,
    ( spl3_4
  <=> sK2 = k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f154,plain,
    ( sK2 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(superposition,[],[f152,f90])).

fof(f152,plain,
    ( sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f148,f49,f150])).

fof(f49,plain,
    ( spl3_1
  <=> sK2 = k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f148,plain,
    ( sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f147,f132])).

fof(f132,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f116,f90])).

fof(f147,plain,
    ( sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f51,f32])).

fof(f51,plain,
    ( sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f62,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f57,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f49])).

fof(f45,plain,(
    sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(definition_unfolding,[],[f23,f38,f43,f43])).

fof(f23,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 15:21:16 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.45  % (12093)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (12089)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (12092)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (12086)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (12087)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (12097)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (12095)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (12100)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (12094)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.56  % (12084)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.56  % (12099)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.57  % (12088)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.57  % (12096)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.57  % (12085)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.57  % (12098)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.67/0.57  % (12090)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.67/0.57  % (12083)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.67/0.58  % (12091)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.80/0.59  % (12089)Refutation found. Thanks to Tanya!
% 1.80/0.59  % SZS status Theorem for theBenchmark
% 1.80/0.59  % SZS output start Proof for theBenchmark
% 1.80/0.59  fof(f1509,plain,(
% 1.80/0.59    $false),
% 1.80/0.59    inference(avatar_sat_refutation,[],[f52,f57,f62,f153,f159,f180,f291,f335,f1407,f1503,f1508])).
% 1.80/0.59  fof(f1508,plain,(
% 1.80/0.59    k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.80/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.80/0.59  fof(f1503,plain,(
% 1.80/0.59    spl3_40 | ~spl3_32),
% 1.80/0.59    inference(avatar_split_clause,[],[f1476,f1404,f1500])).
% 1.80/0.59  fof(f1500,plain,(
% 1.80/0.59    spl3_40 <=> k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.80/0.59  fof(f1404,plain,(
% 1.80/0.59    spl3_32 <=> k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.80/0.59  fof(f1476,plain,(
% 1.80/0.59    k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_32),
% 1.80/0.59    inference(superposition,[],[f566,f1406])).
% 1.80/0.59  fof(f1406,plain,(
% 1.80/0.59    k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_32),
% 1.80/0.59    inference(avatar_component_clause,[],[f1404])).
% 1.80/0.59  fof(f566,plain,(
% 1.80/0.59    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(X6,k2_xboole_0(X6,X7))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f545,f90])).
% 1.80/0.59  fof(f90,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.80/0.59    inference(backward_demodulation,[],[f63,f79])).
% 1.80/0.59  fof(f79,plain,(
% 1.80/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.80/0.59    inference(forward_demodulation,[],[f72,f25])).
% 1.80/0.59  fof(f25,plain,(
% 1.80/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f3])).
% 1.80/0.59  fof(f3,axiom,(
% 1.80/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.80/0.59  fof(f72,plain,(
% 1.80/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.80/0.59    inference(superposition,[],[f63,f24])).
% 1.80/0.59  fof(f24,plain,(
% 1.80/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f5])).
% 1.80/0.59  fof(f5,axiom,(
% 1.80/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.80/0.59  fof(f63,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.80/0.59    inference(superposition,[],[f32,f24])).
% 1.80/0.59  fof(f32,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f4])).
% 1.80/0.59  fof(f4,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.80/0.59  fof(f545,plain,(
% 1.80/0.59    ( ! [X6,X7] : (k2_xboole_0(X6,k2_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(X6,k2_xboole_0(X6,X7)))) )),
% 1.80/0.59    inference(superposition,[],[f89,f218])).
% 1.80/0.59  fof(f218,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.80/0.59    inference(forward_demodulation,[],[f206,f25])).
% 1.80/0.59  fof(f206,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(superposition,[],[f90,f66])).
% 1.80/0.59  fof(f66,plain,(
% 1.80/0.59    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.80/0.59    inference(superposition,[],[f32,f24])).
% 1.80/0.59  fof(f89,plain,(
% 1.80/0.59    ( ! [X6,X4,X5] : (k5_xboole_0(k5_xboole_0(X4,k2_xboole_0(X4,X5)),k5_xboole_0(k2_xboole_0(X4,k2_xboole_0(X4,X5)),X6)) = k5_xboole_0(X4,X6)) )),
% 1.80/0.59    inference(superposition,[],[f32,f46])).
% 1.80/0.59  fof(f46,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 1.80/0.59    inference(definition_unfolding,[],[f26,f30])).
% 1.80/0.59  fof(f30,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f6])).
% 1.80/0.59  fof(f6,axiom,(
% 1.80/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.80/0.59  fof(f26,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f2])).
% 1.80/0.59  fof(f2,axiom,(
% 1.80/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.80/0.59  fof(f1407,plain,(
% 1.80/0.59    spl3_32 | ~spl3_14),
% 1.80/0.59    inference(avatar_split_clause,[],[f1402,f288,f1404])).
% 1.80/0.59  fof(f288,plain,(
% 1.80/0.59    spl3_14 <=> k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.80/0.59  fof(f1402,plain,(
% 1.80/0.59    k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_14),
% 1.80/0.59    inference(forward_demodulation,[],[f290,f235])).
% 1.80/0.59  fof(f235,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 1.80/0.59    inference(superposition,[],[f90,f218])).
% 1.80/0.59  fof(f290,plain,(
% 1.80/0.59    k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_14),
% 1.80/0.59    inference(avatar_component_clause,[],[f288])).
% 1.80/0.59  fof(f335,plain,(
% 1.80/0.59    spl3_19 | ~spl3_7),
% 1.80/0.59    inference(avatar_split_clause,[],[f317,f177,f332])).
% 1.80/0.59  fof(f332,plain,(
% 1.80/0.59    spl3_19 <=> k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.80/0.59  fof(f177,plain,(
% 1.80/0.59    spl3_7 <=> sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.80/0.59  fof(f317,plain,(
% 1.80/0.59    k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_7),
% 1.80/0.59    inference(superposition,[],[f229,f179])).
% 1.80/0.59  fof(f179,plain,(
% 1.80/0.59    sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_7),
% 1.80/0.59    inference(avatar_component_clause,[],[f177])).
% 1.80/0.59  fof(f229,plain,(
% 1.80/0.59    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6) )),
% 1.80/0.59    inference(superposition,[],[f218,f218])).
% 1.80/0.59  fof(f291,plain,(
% 1.80/0.59    spl3_14 | ~spl3_7),
% 1.80/0.59    inference(avatar_split_clause,[],[f282,f177,f288])).
% 1.80/0.59  fof(f282,plain,(
% 1.80/0.59    k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_7),
% 1.80/0.59    inference(superposition,[],[f116,f179])).
% 1.80/0.59  fof(f116,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 1.80/0.59    inference(backward_demodulation,[],[f93,f90])).
% 1.80/0.59  fof(f93,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0)))))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f44,f32])).
% 1.80/0.59  fof(f44,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))))) )),
% 1.80/0.59    inference(definition_unfolding,[],[f29,f38])).
% 1.80/0.59  fof(f38,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.80/0.59    inference(definition_unfolding,[],[f28,f30])).
% 1.80/0.59  fof(f28,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f1])).
% 1.80/0.59  fof(f1,axiom,(
% 1.80/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.80/0.59  fof(f29,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f7])).
% 1.80/0.59  fof(f7,axiom,(
% 1.80/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.80/0.59  fof(f180,plain,(
% 1.80/0.59    spl3_7 | spl3_2 | spl3_3),
% 1.80/0.59    inference(avatar_split_clause,[],[f164,f59,f54,f177])).
% 1.80/0.59  fof(f54,plain,(
% 1.80/0.59    spl3_2 <=> r2_hidden(sK1,sK2)),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.80/0.59  fof(f59,plain,(
% 1.80/0.59    spl3_3 <=> r2_hidden(sK0,sK2)),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.80/0.59  fof(f164,plain,(
% 1.80/0.59    sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (spl3_2 | spl3_3)),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f56,f61,f161])).
% 1.80/0.59  fof(f161,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2) )),
% 1.80/0.59    inference(forward_demodulation,[],[f160,f90])).
% 1.80/0.59  fof(f160,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f47,f32])).
% 1.80/0.59  fof(f47,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k2_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.80/0.59    inference(definition_unfolding,[],[f33,f38,f43])).
% 1.80/0.59  fof(f43,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.80/0.59    inference(definition_unfolding,[],[f27,f42])).
% 1.80/0.59  fof(f42,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.80/0.59    inference(definition_unfolding,[],[f31,f41])).
% 1.80/0.59  fof(f41,plain,(
% 1.80/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.80/0.59    inference(definition_unfolding,[],[f34,f40])).
% 1.80/0.59  fof(f40,plain,(
% 1.80/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.80/0.59    inference(definition_unfolding,[],[f35,f39])).
% 1.80/0.59  fof(f39,plain,(
% 1.80/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.80/0.59    inference(definition_unfolding,[],[f36,f37])).
% 1.80/0.59  fof(f37,plain,(
% 1.80/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f13])).
% 1.80/0.59  fof(f13,axiom,(
% 1.80/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.80/0.59  fof(f36,plain,(
% 1.80/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f12])).
% 1.80/0.59  fof(f12,axiom,(
% 1.80/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.80/0.59  fof(f35,plain,(
% 1.80/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f11])).
% 1.80/0.59  fof(f11,axiom,(
% 1.80/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.80/0.59  fof(f34,plain,(
% 1.80/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f10])).
% 1.80/0.59  fof(f10,axiom,(
% 1.80/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.80/0.59  fof(f31,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f9])).
% 1.80/0.59  fof(f9,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.80/0.59  fof(f27,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f8])).
% 1.80/0.59  fof(f8,axiom,(
% 1.80/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.80/0.59  fof(f33,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f18])).
% 1.80/0.59  fof(f18,plain,(
% 1.80/0.59    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.80/0.59    inference(ennf_transformation,[],[f14])).
% 1.80/0.59  fof(f14,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.80/0.59  fof(f61,plain,(
% 1.80/0.59    ~r2_hidden(sK0,sK2) | spl3_3),
% 1.80/0.59    inference(avatar_component_clause,[],[f59])).
% 1.80/0.59  fof(f56,plain,(
% 1.80/0.59    ~r2_hidden(sK1,sK2) | spl3_2),
% 1.80/0.59    inference(avatar_component_clause,[],[f54])).
% 1.80/0.59  fof(f159,plain,(
% 1.80/0.59    ~spl3_5 | spl3_4),
% 1.80/0.59    inference(avatar_split_clause,[],[f154,f150,f156])).
% 1.80/0.59  fof(f156,plain,(
% 1.80/0.59    spl3_5 <=> sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.80/0.59  fof(f150,plain,(
% 1.80/0.59    spl3_4 <=> sK2 = k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.80/0.59  fof(f154,plain,(
% 1.80/0.59    sK2 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 1.80/0.59    inference(superposition,[],[f152,f90])).
% 1.80/0.59  fof(f152,plain,(
% 1.80/0.59    sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) | spl3_4),
% 1.80/0.59    inference(avatar_component_clause,[],[f150])).
% 1.80/0.59  fof(f153,plain,(
% 1.80/0.59    ~spl3_4 | spl3_1),
% 1.80/0.59    inference(avatar_split_clause,[],[f148,f49,f150])).
% 1.80/0.59  fof(f49,plain,(
% 1.80/0.59    spl3_1 <=> sK2 = k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.80/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.80/0.59  fof(f148,plain,(
% 1.80/0.59    sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) | spl3_1),
% 1.80/0.59    inference(forward_demodulation,[],[f147,f132])).
% 1.80/0.59  fof(f132,plain,(
% 1.80/0.59    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.80/0.59    inference(superposition,[],[f116,f90])).
% 1.80/0.59  fof(f147,plain,(
% 1.80/0.59    sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | spl3_1),
% 1.80/0.59    inference(forward_demodulation,[],[f51,f32])).
% 1.80/0.59  fof(f51,plain,(
% 1.80/0.59    sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_1),
% 1.80/0.59    inference(avatar_component_clause,[],[f49])).
% 1.80/0.59  fof(f62,plain,(
% 1.80/0.59    ~spl3_3),
% 1.80/0.59    inference(avatar_split_clause,[],[f21,f59])).
% 1.80/0.59  fof(f21,plain,(
% 1.80/0.59    ~r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f20])).
% 1.80/0.59  fof(f20,plain,(
% 1.80/0.59    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 1.80/0.59  fof(f19,plain,(
% 1.80/0.59    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f17,plain,(
% 1.80/0.59    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.80/0.59    inference(ennf_transformation,[],[f16])).
% 1.80/0.59  fof(f16,negated_conjecture,(
% 1.80/0.59    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.80/0.59    inference(negated_conjecture,[],[f15])).
% 1.80/0.59  fof(f15,conjecture,(
% 1.80/0.59    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.80/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 1.80/0.59  fof(f57,plain,(
% 1.80/0.59    ~spl3_2),
% 1.80/0.59    inference(avatar_split_clause,[],[f22,f54])).
% 1.80/0.59  fof(f22,plain,(
% 1.80/0.59    ~r2_hidden(sK1,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f20])).
% 1.80/0.59  fof(f52,plain,(
% 1.80/0.59    ~spl3_1),
% 1.80/0.59    inference(avatar_split_clause,[],[f45,f49])).
% 1.80/0.59  fof(f45,plain,(
% 1.80/0.59    sK2 != k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_xboole_0(k5_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k2_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.80/0.59    inference(definition_unfolding,[],[f23,f38,f43,f43])).
% 1.80/0.59  fof(f23,plain,(
% 1.80/0.59    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.80/0.59    inference(cnf_transformation,[],[f20])).
% 1.80/0.59  % SZS output end Proof for theBenchmark
% 1.80/0.59  % (12089)------------------------------
% 1.80/0.59  % (12089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.59  % (12089)Termination reason: Refutation
% 1.80/0.59  
% 1.80/0.59  % (12089)Memory used [KB]: 7547
% 1.80/0.59  % (12089)Time elapsed: 0.138 s
% 1.80/0.59  % (12089)------------------------------
% 1.80/0.59  % (12089)------------------------------
% 1.80/0.60  % (12082)Success in time 0.23 s
%------------------------------------------------------------------------------
