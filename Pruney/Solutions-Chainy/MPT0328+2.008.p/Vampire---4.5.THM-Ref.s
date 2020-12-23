%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 161 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 228 expanded)
%              Number of equality atoms :   73 ( 147 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f98,f121,f131,f177,f183])).

fof(f183,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f180,f173,f128])).

fof(f128,plain,
    ( spl2_5
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f173,plain,
    ( spl2_6
  <=> r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f180,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl2_6 ),
    inference(resolution,[],[f175,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = X0 ) ),
    inference(forward_demodulation,[],[f100,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f33,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f175,plain,
    ( r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f173])).

fof(f177,plain,
    ( spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f171,f118,f173])).

fof(f118,plain,
    ( spl2_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f171,plain,
    ( r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f170])).

fof(f170,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(superposition,[],[f36,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f131,plain,
    ( ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f126,f57,f128])).

fof(f57,plain,
    ( spl2_1
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f126,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f125,f40])).

fof(f125,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_1 ),
    inference(superposition,[],[f59,f40])).

fof(f59,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f121,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f116,f94,f118])).

fof(f94,plain,
    ( spl2_3
  <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f116,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f110,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f110,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f88,f96])).

fof(f96,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f74,f66])).

fof(f66,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f40,f27])).

fof(f98,plain,
    ( spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f92,f62,f94])).

fof(f62,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_2 ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 ) ),
    inference(definition_unfolding,[],[f38,f33,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f65,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f62])).

fof(f25,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f60,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f52,f57])).

fof(f52,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f26,f33,f45,f51,f51])).

fof(f26,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:13:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (1957)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (1959)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (1962)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (1973)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (1961)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1967)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (1971)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (1964)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (1968)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (1958)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (1968)Refutation not found, incomplete strategy% (1968)------------------------------
% 0.21/0.48  % (1968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1968)Memory used [KB]: 10618
% 0.21/0.48  % (1968)Time elapsed: 0.078 s
% 0.21/0.48  % (1968)------------------------------
% 0.21/0.48  % (1968)------------------------------
% 0.21/0.48  % (1960)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (1963)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (1974)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (1963)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f65,f98,f121,f131,f177,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl2_5 | ~spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f180,f173,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl2_5 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl2_6 <=> r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl2_6),
% 0.21/0.49    inference(resolution,[],[f175,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f100,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f53,f40])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f33,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f173])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl2_6 | ~spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f171,f118,f173])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl2_4 <=> k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 0.21/0.49    inference(superposition,[],[f36,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~spl2_5 | spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f57,f128])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl2_1 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | spl2_1),
% 0.21/0.49    inference(forward_demodulation,[],[f125,f40])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    sK1 != k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl2_1),
% 0.21/0.49    inference(superposition,[],[f59,f40])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl2_4 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f116,f94,f118])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl2_3 <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_3),
% 0.21/0.49    inference(forward_demodulation,[],[f110,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,sK1) | ~spl2_3),
% 0.21/0.49    inference(superposition,[],[f88,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.49    inference(forward_demodulation,[],[f74,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.49    inference(superposition,[],[f30,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(superposition,[],[f40,f27])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl2_3 | spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f62,f94])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl2_2),
% 0.21/0.49    inference(resolution,[],[f54,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1) | spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f38,f33,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f29,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f31,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f39,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f42,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f43,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f62])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1)) => (sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.49    inference(negated_conjecture,[],[f17])).
% 0.21/0.49  fof(f17,conjecture,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f57])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.49    inference(definition_unfolding,[],[f26,f33,f45,f51,f51])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1963)------------------------------
% 0.21/0.49  % (1963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1963)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1963)Memory used [KB]: 6140
% 0.21/0.49  % (1963)Time elapsed: 0.035 s
% 0.21/0.49  % (1963)------------------------------
% 0.21/0.49  % (1963)------------------------------
% 0.21/0.49  % (1956)Success in time 0.132 s
%------------------------------------------------------------------------------
