%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:32 EST 2020

% Result     : Theorem 3.81s
% Output     : Refutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  152 (1155 expanded)
%              Number of leaves         :   28 ( 411 expanded)
%              Depth                    :   19
%              Number of atoms          :  302 (1437 expanded)
%              Number of equality atoms :  166 (1233 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3699,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f100,f101,f102,f103,f299,f327,f330,f2467,f3050,f3089,f3093,f3104,f3311,f3695,f3698])).

fof(f3698,plain,
    ( spl3_5
    | spl3_2
    | spl3_3
    | spl3_4
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f3696,f3692,f92,f88,f84,f96])).

fof(f96,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( spl3_2
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f88,plain,
    ( spl3_3
  <=> sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( spl3_4
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f3692,plain,
    ( spl3_56
  <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f3696,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ spl3_56 ),
    inference(resolution,[],[f3694,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f59,f59,f55,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f55])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f3694,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f3692])).

fof(f3695,plain,
    ( spl3_56
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f3662,f3308,f3692])).

fof(f3308,plain,
    ( spl3_50
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f3662,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_50 ),
    inference(superposition,[],[f67,f3310])).

fof(f3310,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f3308])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3311,plain,
    ( spl3_50
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3306,f292,f3308])).

fof(f292,plain,
    ( spl3_10
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f3306,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f3305,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3305,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f3250,f126])).

fof(f126,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f104,f120])).

fof(f120,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f113,f32])).

fof(f113,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f104,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3250,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)))
    | ~ spl3_10 ),
    inference(superposition,[],[f3180,f30])).

fof(f3180,plain,
    ( ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0)))) = X0
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f3179,f120])).

fof(f3179,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0))))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f3178,f42])).

fof(f3178,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),X0)))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f3114,f42])).

fof(f3114,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))),X0))
    | ~ spl3_10 ),
    inference(superposition,[],[f42,f294])).

fof(f294,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f292])).

fof(f3104,plain,(
    spl3_42 ),
    inference(avatar_contradiction_clause,[],[f3103])).

fof(f3103,plain,
    ( $false
    | spl3_42 ),
    inference(trivial_inequality_removal,[],[f3096])).

fof(f3096,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_42 ),
    inference(superposition,[],[f3088,f120])).

fof(f3088,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f3086])).

fof(f3086,plain,
    ( spl3_42
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f3093,plain,
    ( spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f3092,f80,f292])).

fof(f80,plain,
    ( spl3_1
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f3092,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f82,f42])).

fof(f82,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f3089,plain,
    ( ~ spl3_42
    | ~ spl3_5
    | spl3_10 ),
    inference(avatar_split_clause,[],[f3084,f292,f96,f3086])).

fof(f3084,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | spl3_10 ),
    inference(forward_demodulation,[],[f3083,f30])).

fof(f3083,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ spl3_5
    | spl3_10 ),
    inference(forward_demodulation,[],[f3082,f406])).

fof(f406,plain,(
    ! [X4,X3] : k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) ),
    inference(resolution,[],[f382,f78])).

fof(f78,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f382,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(backward_demodulation,[],[f273,f381])).

fof(f381,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(forward_demodulation,[],[f380,f126])).

fof(f380,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) ),
    inference(forward_demodulation,[],[f68,f42])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f38,f56,f58,f56])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = X1 ) ),
    inference(forward_demodulation,[],[f272,f126])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f69,f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) = X1 ) ),
    inference(definition_unfolding,[],[f41,f56,f58])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f3082,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))
    | ~ spl3_5
    | spl3_10 ),
    inference(forward_demodulation,[],[f3081,f120])).

fof(f3081,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | ~ spl3_5
    | spl3_10 ),
    inference(forward_demodulation,[],[f293,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f293,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f292])).

fof(f3050,plain,
    ( ~ spl3_13
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f3049,f292,f92,f324])).

fof(f324,plain,
    ( spl3_13
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f3049,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | ~ spl3_4
    | spl3_10 ),
    inference(forward_demodulation,[],[f3048,f32])).

fof(f3048,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_4
    | spl3_10 ),
    inference(forward_demodulation,[],[f3040,f30])).

fof(f3040,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | ~ spl3_4
    | spl3_10 ),
    inference(backward_demodulation,[],[f293,f2495])).

fof(f2495,plain,
    ( ! [X5] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X5) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X5)))
    | ~ spl3_4 ),
    inference(superposition,[],[f409,f94])).

fof(f94,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f409,plain,(
    ! [X8,X7] : k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(resolution,[],[f382,f77])).

fof(f77,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f59,f55])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2467,plain,
    ( ~ spl3_13
    | ~ spl3_3
    | spl3_10 ),
    inference(avatar_split_clause,[],[f2466,f292,f88,f324])).

fof(f2466,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | ~ spl3_3
    | spl3_10 ),
    inference(forward_demodulation,[],[f2465,f32])).

fof(f2465,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_3
    | spl3_10 ),
    inference(forward_demodulation,[],[f2457,f30])).

fof(f2457,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | ~ spl3_3
    | spl3_10 ),
    inference(backward_demodulation,[],[f293,f447])).

fof(f447,plain,
    ( ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f336,f382])).

fof(f336,plain,
    ( ! [X1] : r1_tarski(sK0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f76,f90])).

fof(f90,plain,
    ( sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f76,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f59,f55])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f330,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl3_13 ),
    inference(trivial_inequality_removal,[],[f328])).

fof(f328,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_13 ),
    inference(superposition,[],[f326,f30])).

fof(f326,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f324])).

fof(f327,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | spl3_10 ),
    inference(avatar_split_clause,[],[f322,f292,f84,f324])).

fof(f322,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | ~ spl3_2
    | spl3_10 ),
    inference(forward_demodulation,[],[f321,f65])).

fof(f65,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f59])).

fof(f31,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f321,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_2
    | spl3_10 ),
    inference(forward_demodulation,[],[f320,f126])).

fof(f320,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl3_2
    | spl3_10 ),
    inference(forward_demodulation,[],[f293,f86])).

fof(f86,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f299,plain,
    ( ~ spl3_10
    | spl3_1 ),
    inference(avatar_split_clause,[],[f298,f80,f292])).

fof(f298,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f81,f42])).

fof(f81,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f103,plain,
    ( ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f64,f96,f80])).

fof(f64,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f25,f58,f55])).

fof(f25,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f102,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f92,f80])).

fof(f63,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f26,f59,f58,f55])).

fof(f26,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f62,f88,f80])).

fof(f62,plain,
    ( sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f27,f59,f58,f55])).

fof(f27,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f61,f84,f80])).

fof(f61,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f28,f55,f58,f55])).

fof(f28,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( spl3_1
    | spl3_2
    | spl3_3
    | spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f60,f96,f92,f88,f84,f80])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f29,f59,f59,f55,f58,f55])).

fof(f29,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:04:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (8062)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (8070)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (8062)Refutation not found, incomplete strategy% (8062)------------------------------
% 0.22/0.51  % (8062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8062)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8062)Memory used [KB]: 6140
% 0.22/0.51  % (8062)Time elapsed: 0.006 s
% 0.22/0.51  % (8062)------------------------------
% 0.22/0.51  % (8062)------------------------------
% 0.22/0.51  % (8054)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (8050)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (8052)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (8056)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (8074)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (8056)Refutation not found, incomplete strategy% (8056)------------------------------
% 0.22/0.53  % (8056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8056)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8056)Memory used [KB]: 10618
% 0.22/0.53  % (8056)Time elapsed: 0.107 s
% 0.22/0.53  % (8056)------------------------------
% 0.22/0.53  % (8056)------------------------------
% 0.22/0.53  % (8053)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (8068)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (8058)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (8066)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (8060)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (8067)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (8051)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (8048)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (8061)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (8059)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (8049)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (8073)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (8071)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (8065)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (8075)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (8058)Refutation not found, incomplete strategy% (8058)------------------------------
% 0.22/0.55  % (8058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8076)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (8068)Refutation not found, incomplete strategy% (8068)------------------------------
% 0.22/0.55  % (8068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8068)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8068)Memory used [KB]: 1791
% 0.22/0.55  % (8068)Time elapsed: 0.123 s
% 0.22/0.55  % (8068)------------------------------
% 0.22/0.55  % (8068)------------------------------
% 0.22/0.56  % (8069)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (8058)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8058)Memory used [KB]: 10618
% 0.22/0.56  % (8058)Time elapsed: 0.144 s
% 0.22/0.56  % (8058)------------------------------
% 0.22/0.56  % (8058)------------------------------
% 0.22/0.56  % (8057)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (8072)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (8047)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (8064)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (8064)Refutation not found, incomplete strategy% (8064)------------------------------
% 0.22/0.57  % (8064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8064)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8064)Memory used [KB]: 10618
% 0.22/0.57  % (8064)Time elapsed: 0.149 s
% 0.22/0.57  % (8064)------------------------------
% 0.22/0.57  % (8064)------------------------------
% 0.22/0.57  % (8057)Refutation not found, incomplete strategy% (8057)------------------------------
% 0.22/0.57  % (8057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8057)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8057)Memory used [KB]: 10618
% 0.22/0.57  % (8057)Time elapsed: 0.148 s
% 0.22/0.57  % (8057)------------------------------
% 0.22/0.57  % (8057)------------------------------
% 0.22/0.57  % (8055)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.59  % (8063)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.59  % (8047)Refutation not found, incomplete strategy% (8047)------------------------------
% 0.22/0.59  % (8047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8047)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8047)Memory used [KB]: 1663
% 0.22/0.59  % (8047)Time elapsed: 0.142 s
% 0.22/0.59  % (8047)------------------------------
% 0.22/0.59  % (8047)------------------------------
% 0.22/0.59  % (8072)Refutation not found, incomplete strategy% (8072)------------------------------
% 0.22/0.59  % (8072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8072)Memory used [KB]: 7036
% 0.22/0.59  % (8072)Time elapsed: 0.160 s
% 0.22/0.59  % (8072)------------------------------
% 0.22/0.59  % (8072)------------------------------
% 2.23/0.67  % (8080)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.75/0.73  % (8081)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.75/0.77  % (8082)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.07/0.77  % (8098)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.07/0.78  % (8069)Refutation not found, incomplete strategy% (8069)------------------------------
% 3.07/0.78  % (8069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.78  % (8069)Termination reason: Refutation not found, incomplete strategy
% 3.07/0.78  
% 3.07/0.78  % (8069)Memory used [KB]: 16758
% 3.07/0.78  % (8069)Time elapsed: 0.344 s
% 3.07/0.78  % (8069)------------------------------
% 3.07/0.78  % (8069)------------------------------
% 3.07/0.78  % (8083)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.07/0.81  % (8087)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.07/0.81  % (8089)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.63/0.85  % (8052)Time limit reached!
% 3.63/0.85  % (8052)------------------------------
% 3.63/0.85  % (8052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.85  % (8052)Termination reason: Time limit
% 3.63/0.85  
% 3.63/0.85  % (8052)Memory used [KB]: 8955
% 3.63/0.85  % (8052)Time elapsed: 0.428 s
% 3.63/0.85  % (8052)------------------------------
% 3.63/0.85  % (8052)------------------------------
% 3.63/0.86  % (8109)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.81/0.89  % (8063)Refutation found. Thanks to Tanya!
% 3.81/0.89  % SZS status Theorem for theBenchmark
% 3.81/0.89  % SZS output start Proof for theBenchmark
% 3.81/0.89  fof(f3699,plain,(
% 3.81/0.89    $false),
% 3.81/0.89    inference(avatar_sat_refutation,[],[f99,f100,f101,f102,f103,f299,f327,f330,f2467,f3050,f3089,f3093,f3104,f3311,f3695,f3698])).
% 3.81/0.89  fof(f3698,plain,(
% 3.81/0.89    spl3_5 | spl3_2 | spl3_3 | spl3_4 | ~spl3_56),
% 3.81/0.89    inference(avatar_split_clause,[],[f3696,f3692,f92,f88,f84,f96])).
% 3.81/0.89  fof(f96,plain,(
% 3.81/0.89    spl3_5 <=> k1_xboole_0 = sK0),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.81/0.89  fof(f84,plain,(
% 3.81/0.89    spl3_2 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.81/0.89  fof(f88,plain,(
% 3.81/0.89    spl3_3 <=> sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.81/0.89  fof(f92,plain,(
% 3.81/0.89    spl3_4 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.81/0.89  fof(f3692,plain,(
% 3.81/0.89    spl3_56 <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 3.81/0.89  fof(f3696,plain,(
% 3.81/0.89    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k1_xboole_0 = sK0 | ~spl3_56),
% 3.81/0.89    inference(resolution,[],[f3694,f74])).
% 3.81/0.89  fof(f74,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 3.81/0.89    inference(definition_unfolding,[],[f43,f59,f59,f55,f55])).
% 3.81/0.89  fof(f55,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.81/0.89    inference(definition_unfolding,[],[f39,f54])).
% 3.81/0.89  fof(f54,plain,(
% 3.81/0.89    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.81/0.89    inference(definition_unfolding,[],[f48,f53])).
% 3.81/0.89  fof(f53,plain,(
% 3.81/0.89    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.81/0.89    inference(definition_unfolding,[],[f49,f52])).
% 3.81/0.89  fof(f52,plain,(
% 3.81/0.89    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.81/0.89    inference(definition_unfolding,[],[f50,f51])).
% 3.81/0.89  fof(f51,plain,(
% 3.81/0.89    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f14])).
% 3.81/0.89  fof(f14,axiom,(
% 3.81/0.89    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.81/0.89  fof(f50,plain,(
% 3.81/0.89    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f13])).
% 3.81/0.89  fof(f13,axiom,(
% 3.81/0.89    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.81/0.89  fof(f49,plain,(
% 3.81/0.89    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f12])).
% 3.81/0.89  fof(f12,axiom,(
% 3.81/0.89    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.81/0.89  fof(f48,plain,(
% 3.81/0.89    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f11])).
% 3.81/0.89  fof(f11,axiom,(
% 3.81/0.89    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.81/0.89  fof(f39,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f15])).
% 3.81/0.89  fof(f15,axiom,(
% 3.81/0.89    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 3.81/0.89  fof(f59,plain,(
% 3.81/0.89    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.81/0.89    inference(definition_unfolding,[],[f33,f55])).
% 3.81/0.89  fof(f33,plain,(
% 3.81/0.89    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f10])).
% 3.81/0.89  fof(f10,axiom,(
% 3.81/0.89    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.81/0.89  fof(f43,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f24])).
% 3.81/0.89  fof(f24,plain,(
% 3.81/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.81/0.89    inference(ennf_transformation,[],[f18])).
% 3.81/0.89  fof(f18,axiom,(
% 3.81/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 3.81/0.89  fof(f3694,plain,(
% 3.81/0.89    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_56),
% 3.81/0.89    inference(avatar_component_clause,[],[f3692])).
% 3.81/0.89  fof(f3695,plain,(
% 3.81/0.89    spl3_56 | ~spl3_50),
% 3.81/0.89    inference(avatar_split_clause,[],[f3662,f3308,f3692])).
% 3.81/0.89  fof(f3308,plain,(
% 3.81/0.89    spl3_50 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 3.81/0.89  fof(f3662,plain,(
% 3.81/0.89    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_50),
% 3.81/0.89    inference(superposition,[],[f67,f3310])).
% 3.81/0.89  fof(f3310,plain,(
% 3.81/0.89    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~spl3_50),
% 3.81/0.89    inference(avatar_component_clause,[],[f3308])).
% 3.81/0.89  fof(f67,plain,(
% 3.81/0.89    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f35,f56])).
% 3.81/0.89  fof(f56,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f36,f55])).
% 3.81/0.89  fof(f36,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f16])).
% 3.81/0.89  fof(f16,axiom,(
% 3.81/0.89    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.81/0.89  fof(f35,plain,(
% 3.81/0.89    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f6])).
% 3.81/0.89  fof(f6,axiom,(
% 3.81/0.89    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.81/0.89  fof(f3311,plain,(
% 3.81/0.89    spl3_50 | ~spl3_10),
% 3.81/0.89    inference(avatar_split_clause,[],[f3306,f292,f3308])).
% 3.81/0.89  fof(f292,plain,(
% 3.81/0.89    spl3_10 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 3.81/0.89  fof(f3306,plain,(
% 3.81/0.89    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~spl3_10),
% 3.81/0.89    inference(forward_demodulation,[],[f3305,f32])).
% 3.81/0.89  fof(f32,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.81/0.89    inference(cnf_transformation,[],[f5])).
% 3.81/0.89  fof(f5,axiom,(
% 3.81/0.89    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 3.81/0.89  fof(f3305,plain,(
% 3.81/0.89    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) | ~spl3_10),
% 3.81/0.89    inference(forward_demodulation,[],[f3250,f126])).
% 3.81/0.89  fof(f126,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.81/0.89    inference(backward_demodulation,[],[f104,f120])).
% 3.81/0.89  fof(f120,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.81/0.89    inference(forward_demodulation,[],[f113,f32])).
% 3.81/0.89  fof(f113,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 3.81/0.89    inference(superposition,[],[f104,f30])).
% 3.81/0.89  fof(f30,plain,(
% 3.81/0.89    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f8])).
% 3.81/0.89  fof(f8,axiom,(
% 3.81/0.89    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.81/0.89  fof(f104,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 3.81/0.89    inference(superposition,[],[f42,f30])).
% 3.81/0.89  fof(f42,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f7])).
% 3.81/0.89  fof(f7,axiom,(
% 3.81/0.89    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.81/0.89  fof(f3250,plain,(
% 3.81/0.89    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0))) | ~spl3_10),
% 3.81/0.89    inference(superposition,[],[f3180,f30])).
% 3.81/0.89  fof(f3180,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0)))) = X0) ) | ~spl3_10),
% 3.81/0.89    inference(forward_demodulation,[],[f3179,f120])).
% 3.81/0.89  fof(f3179,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0))))) ) | ~spl3_10),
% 3.81/0.89    inference(forward_demodulation,[],[f3178,f42])).
% 3.81/0.89  fof(f3178,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),X0)))) ) | ~spl3_10),
% 3.81/0.89    inference(forward_demodulation,[],[f3114,f42])).
% 3.81/0.89  fof(f3114,plain,(
% 3.81/0.89    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))),X0))) ) | ~spl3_10),
% 3.81/0.89    inference(superposition,[],[f42,f294])).
% 3.81/0.89  fof(f294,plain,(
% 3.81/0.89    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | ~spl3_10),
% 3.81/0.89    inference(avatar_component_clause,[],[f292])).
% 3.81/0.89  fof(f3104,plain,(
% 3.81/0.89    spl3_42),
% 3.81/0.89    inference(avatar_contradiction_clause,[],[f3103])).
% 3.81/0.89  fof(f3103,plain,(
% 3.81/0.89    $false | spl3_42),
% 3.81/0.89    inference(trivial_inequality_removal,[],[f3096])).
% 3.81/0.89  fof(f3096,plain,(
% 3.81/0.89    k1_xboole_0 != k1_xboole_0 | spl3_42),
% 3.81/0.89    inference(superposition,[],[f3088,f120])).
% 3.81/0.89  fof(f3088,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | spl3_42),
% 3.81/0.89    inference(avatar_component_clause,[],[f3086])).
% 3.81/0.89  fof(f3086,plain,(
% 3.81/0.89    spl3_42 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 3.81/0.89  fof(f3093,plain,(
% 3.81/0.89    spl3_10 | ~spl3_1),
% 3.81/0.89    inference(avatar_split_clause,[],[f3092,f80,f292])).
% 3.81/0.89  fof(f80,plain,(
% 3.81/0.89    spl3_1 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.81/0.89  fof(f3092,plain,(
% 3.81/0.89    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | ~spl3_1),
% 3.81/0.89    inference(forward_demodulation,[],[f82,f42])).
% 3.81/0.89  fof(f82,plain,(
% 3.81/0.89    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) | ~spl3_1),
% 3.81/0.89    inference(avatar_component_clause,[],[f80])).
% 3.81/0.89  fof(f3089,plain,(
% 3.81/0.89    ~spl3_42 | ~spl3_5 | spl3_10),
% 3.81/0.89    inference(avatar_split_clause,[],[f3084,f292,f96,f3086])).
% 3.81/0.89  fof(f3084,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_5 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f3083,f30])).
% 3.81/0.89  fof(f3083,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | (~spl3_5 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f3082,f406])).
% 3.81/0.89  fof(f406,plain,(
% 3.81/0.89    ( ! [X4,X3] : (k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))) )),
% 3.81/0.89    inference(resolution,[],[f382,f78])).
% 3.81/0.89  fof(f78,plain,(
% 3.81/0.89    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.81/0.89    inference(equality_resolution,[],[f73])).
% 3.81/0.89  fof(f73,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f44,f55])).
% 3.81/0.89  fof(f44,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f24])).
% 3.81/0.89  fof(f382,plain,(
% 3.81/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 3.81/0.89    inference(backward_demodulation,[],[f273,f381])).
% 3.81/0.89  fof(f381,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) )),
% 3.81/0.89    inference(forward_demodulation,[],[f380,f126])).
% 3.81/0.89  fof(f380,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))))) )),
% 3.81/0.89    inference(forward_demodulation,[],[f68,f42])).
% 3.81/0.89  fof(f68,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f38,f56,f58,f56])).
% 3.81/0.89  fof(f58,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f37,f57])).
% 3.81/0.89  fof(f57,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f40,f56])).
% 3.81/0.89  fof(f40,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f9])).
% 3.81/0.89  fof(f9,axiom,(
% 3.81/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.81/0.89  fof(f37,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f2])).
% 3.81/0.89  fof(f2,axiom,(
% 3.81/0.89    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.81/0.89  fof(f38,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.81/0.89    inference(cnf_transformation,[],[f3])).
% 3.81/0.89  fof(f3,axiom,(
% 3.81/0.89    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.81/0.89  fof(f273,plain,(
% 3.81/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = X1) )),
% 3.81/0.89    inference(forward_demodulation,[],[f272,f126])).
% 3.81/0.89  fof(f272,plain,(
% 3.81/0.89    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) = X1 | ~r1_tarski(X0,X1)) )),
% 3.81/0.89    inference(forward_demodulation,[],[f69,f42])).
% 3.81/0.89  fof(f69,plain,(
% 3.81/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) = X1) )),
% 3.81/0.89    inference(definition_unfolding,[],[f41,f56,f58])).
% 3.81/0.89  fof(f41,plain,(
% 3.81/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 3.81/0.89    inference(cnf_transformation,[],[f23])).
% 3.81/0.89  fof(f23,plain,(
% 3.81/0.89    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.81/0.89    inference(ennf_transformation,[],[f4])).
% 3.81/0.89  fof(f4,axiom,(
% 3.81/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 3.81/0.89  fof(f3082,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) | (~spl3_5 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f3081,f120])).
% 3.81/0.89  fof(f3081,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | (~spl3_5 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f293,f98])).
% 3.81/0.89  fof(f98,plain,(
% 3.81/0.89    k1_xboole_0 = sK0 | ~spl3_5),
% 3.81/0.89    inference(avatar_component_clause,[],[f96])).
% 3.81/0.89  fof(f293,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | spl3_10),
% 3.81/0.89    inference(avatar_component_clause,[],[f292])).
% 3.81/0.89  fof(f3050,plain,(
% 3.81/0.89    ~spl3_13 | ~spl3_4 | spl3_10),
% 3.81/0.89    inference(avatar_split_clause,[],[f3049,f292,f92,f324])).
% 3.81/0.89  fof(f324,plain,(
% 3.81/0.89    spl3_13 <=> k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 3.81/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.81/0.89  fof(f3049,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,sK0) | (~spl3_4 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f3048,f32])).
% 3.81/0.89  fof(f3048,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | (~spl3_4 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f3040,f30])).
% 3.81/0.89  fof(f3040,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | (~spl3_4 | spl3_10)),
% 3.81/0.89    inference(backward_demodulation,[],[f293,f2495])).
% 3.81/0.89  fof(f2495,plain,(
% 3.81/0.89    ( ! [X5] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X5) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X5)))) ) | ~spl3_4),
% 3.81/0.89    inference(superposition,[],[f409,f94])).
% 3.81/0.89  fof(f94,plain,(
% 3.81/0.89    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_4),
% 3.81/0.89    inference(avatar_component_clause,[],[f92])).
% 3.81/0.89  fof(f409,plain,(
% 3.81/0.89    ( ! [X8,X7] : (k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))) )),
% 3.81/0.89    inference(resolution,[],[f382,f77])).
% 3.81/0.89  fof(f77,plain,(
% 3.81/0.89    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.81/0.89    inference(equality_resolution,[],[f72])).
% 3.81/0.89  fof(f72,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f45,f59,f55])).
% 3.81/0.89  fof(f45,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f24])).
% 3.81/0.89  fof(f2467,plain,(
% 3.81/0.89    ~spl3_13 | ~spl3_3 | spl3_10),
% 3.81/0.89    inference(avatar_split_clause,[],[f2466,f292,f88,f324])).
% 3.81/0.89  fof(f2466,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,sK0) | (~spl3_3 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f2465,f32])).
% 3.81/0.89  fof(f2465,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | (~spl3_3 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f2457,f30])).
% 3.81/0.89  fof(f2457,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | (~spl3_3 | spl3_10)),
% 3.81/0.89    inference(backward_demodulation,[],[f293,f447])).
% 3.81/0.89  fof(f447,plain,(
% 3.81/0.89    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2)))) ) | ~spl3_3),
% 3.81/0.89    inference(resolution,[],[f336,f382])).
% 3.81/0.89  fof(f336,plain,(
% 3.81/0.89    ( ! [X1] : (r1_tarski(sK0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2))) ) | ~spl3_3),
% 3.81/0.89    inference(superposition,[],[f76,f90])).
% 3.81/0.89  fof(f90,plain,(
% 3.81/0.89    sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_3),
% 3.81/0.89    inference(avatar_component_clause,[],[f88])).
% 3.81/0.89  fof(f76,plain,(
% 3.81/0.89    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.81/0.89    inference(equality_resolution,[],[f71])).
% 3.81/0.89  fof(f71,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.81/0.89    inference(definition_unfolding,[],[f46,f59,f55])).
% 3.81/0.89  fof(f46,plain,(
% 3.81/0.89    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.81/0.89    inference(cnf_transformation,[],[f24])).
% 3.81/0.89  fof(f330,plain,(
% 3.81/0.89    spl3_13),
% 3.81/0.89    inference(avatar_contradiction_clause,[],[f329])).
% 3.81/0.89  fof(f329,plain,(
% 3.81/0.89    $false | spl3_13),
% 3.81/0.89    inference(trivial_inequality_removal,[],[f328])).
% 3.81/0.89  fof(f328,plain,(
% 3.81/0.89    k1_xboole_0 != k1_xboole_0 | spl3_13),
% 3.81/0.89    inference(superposition,[],[f326,f30])).
% 3.81/0.89  fof(f326,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,sK0) | spl3_13),
% 3.81/0.89    inference(avatar_component_clause,[],[f324])).
% 3.81/0.89  fof(f327,plain,(
% 3.81/0.89    ~spl3_13 | ~spl3_2 | spl3_10),
% 3.81/0.89    inference(avatar_split_clause,[],[f322,f292,f84,f324])).
% 3.81/0.89  fof(f322,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,sK0) | (~spl3_2 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f321,f65])).
% 3.81/0.89  fof(f65,plain,(
% 3.81/0.89    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.81/0.89    inference(definition_unfolding,[],[f31,f59])).
% 3.81/0.89  fof(f31,plain,(
% 3.81/0.89    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 3.81/0.89    inference(cnf_transformation,[],[f17])).
% 3.81/0.89  fof(f17,axiom,(
% 3.81/0.89    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 3.81/0.89  fof(f321,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl3_2 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f320,f126])).
% 3.81/0.89  fof(f320,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | (~spl3_2 | spl3_10)),
% 3.81/0.89    inference(forward_demodulation,[],[f293,f86])).
% 3.81/0.89  fof(f86,plain,(
% 3.81/0.89    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl3_2),
% 3.81/0.89    inference(avatar_component_clause,[],[f84])).
% 3.81/0.89  fof(f299,plain,(
% 3.81/0.89    ~spl3_10 | spl3_1),
% 3.81/0.89    inference(avatar_split_clause,[],[f298,f80,f292])).
% 3.81/0.89  fof(f298,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | spl3_1),
% 3.81/0.89    inference(forward_demodulation,[],[f81,f42])).
% 3.81/0.89  fof(f81,plain,(
% 3.81/0.89    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) | spl3_1),
% 3.81/0.89    inference(avatar_component_clause,[],[f80])).
% 3.81/0.89  fof(f103,plain,(
% 3.81/0.89    ~spl3_1 | ~spl3_5),
% 3.81/0.89    inference(avatar_split_clause,[],[f64,f96,f80])).
% 3.81/0.89  fof(f64,plain,(
% 3.81/0.89    k1_xboole_0 != sK0 | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 3.81/0.89    inference(definition_unfolding,[],[f25,f58,f55])).
% 3.81/0.89  fof(f25,plain,(
% 3.81/0.89    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 3.81/0.89    inference(cnf_transformation,[],[f22])).
% 3.81/0.89  fof(f22,plain,(
% 3.81/0.89    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.81/0.89    inference(ennf_transformation,[],[f20])).
% 3.81/0.89  fof(f20,negated_conjecture,(
% 3.81/0.89    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.81/0.89    inference(negated_conjecture,[],[f19])).
% 3.81/0.89  fof(f19,conjecture,(
% 3.81/0.89    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.81/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 3.81/0.89  fof(f102,plain,(
% 3.81/0.89    ~spl3_1 | ~spl3_4),
% 3.81/0.89    inference(avatar_split_clause,[],[f63,f92,f80])).
% 3.81/0.89  fof(f63,plain,(
% 3.81/0.89    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 3.81/0.89    inference(definition_unfolding,[],[f26,f59,f58,f55])).
% 3.81/0.89  fof(f26,plain,(
% 3.81/0.89    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 3.81/0.89    inference(cnf_transformation,[],[f22])).
% 3.81/0.89  fof(f101,plain,(
% 3.81/0.89    ~spl3_1 | ~spl3_3),
% 3.81/0.89    inference(avatar_split_clause,[],[f62,f88,f80])).
% 3.81/0.89  fof(f62,plain,(
% 3.81/0.89    sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 3.81/0.89    inference(definition_unfolding,[],[f27,f59,f58,f55])).
% 3.81/0.89  fof(f27,plain,(
% 3.81/0.89    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 3.81/0.89    inference(cnf_transformation,[],[f22])).
% 3.81/0.89  fof(f100,plain,(
% 3.81/0.89    ~spl3_1 | ~spl3_2),
% 3.81/0.89    inference(avatar_split_clause,[],[f61,f84,f80])).
% 3.81/0.89  fof(f61,plain,(
% 3.81/0.89    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 3.81/0.89    inference(definition_unfolding,[],[f28,f55,f58,f55])).
% 3.81/0.89  fof(f28,plain,(
% 3.81/0.89    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 3.81/0.89    inference(cnf_transformation,[],[f22])).
% 3.81/0.89  fof(f99,plain,(
% 3.81/0.89    spl3_1 | spl3_2 | spl3_3 | spl3_4 | spl3_5),
% 3.81/0.89    inference(avatar_split_clause,[],[f60,f96,f92,f88,f84,f80])).
% 3.81/0.89  fof(f60,plain,(
% 3.81/0.89    k1_xboole_0 = sK0 | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 3.81/0.89    inference(definition_unfolding,[],[f29,f59,f59,f55,f58,f55])).
% 3.81/0.89  fof(f29,plain,(
% 3.81/0.89    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 3.81/0.89    inference(cnf_transformation,[],[f22])).
% 3.81/0.89  % SZS output end Proof for theBenchmark
% 3.81/0.89  % (8063)------------------------------
% 3.81/0.89  % (8063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.89  % (8063)Termination reason: Refutation
% 3.81/0.89  
% 3.81/0.89  % (8063)Memory used [KB]: 15863
% 3.81/0.89  % (8063)Time elapsed: 0.450 s
% 3.81/0.89  % (8063)------------------------------
% 3.81/0.89  % (8063)------------------------------
% 3.81/0.90  % (8046)Success in time 0.523 s
%------------------------------------------------------------------------------
