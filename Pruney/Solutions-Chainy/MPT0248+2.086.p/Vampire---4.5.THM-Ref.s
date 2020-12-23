%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:02 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 477 expanded)
%              Number of leaves         :   29 ( 177 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 ( 655 expanded)
%              Number of equality atoms :  114 ( 533 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f764,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f90,f95,f215,f273,f325,f711,f721,f741,f757,f763])).

fof(f763,plain,
    ( spl3_5
    | spl3_10
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f762,f754,f82,f294,f92])).

fof(f92,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f294,plain,
    ( spl3_10
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f82,plain,
    ( spl3_3
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f754,plain,
    ( spl3_19
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f762,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(resolution,[],[f288,f756])).

fof(f756,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f754])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_3 ),
    inference(superposition,[],[f69,f83])).

fof(f83,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f57,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f757,plain,
    ( spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f752,f738,f754])).

fof(f738,plain,
    ( spl3_17
  <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f752,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f744,f122])).

fof(f122,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f118,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f118,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f104,f96])).

fof(f96,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f36,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f104,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f45,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f744,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f193,f740])).

fof(f740,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f738])).

fof(f193,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f65,f45])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f741,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f736,f82,f73,f738])).

fof(f73,plain,
    ( spl3_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f736,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f75,f83])).

fof(f75,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f721,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f287,f82,f78,f294])).

fof(f78,plain,
    ( spl3_2
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f287,plain,
    ( sK1 != sK2
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f80,f83])).

fof(f80,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f711,plain,
    ( spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f707,f278,f78])).

fof(f278,plain,
    ( spl3_8
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f707,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f280,f631])).

fof(f631,plain,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f630,f63])).

fof(f63,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f55])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f630,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(forward_demodulation,[],[f601,f118])).

fof(f601,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
    inference(superposition,[],[f505,f29])).

fof(f505,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) ),
    inference(forward_demodulation,[],[f66,f45])).

fof(f66,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f40,f55,f55,f56])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f280,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f278])).

fof(f325,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f324,f87,f73,f278])).

fof(f87,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f324,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f75,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f273,plain,
    ( spl3_4
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f272,f212,f82,f87])).

fof(f212,plain,
    ( spl3_7
  <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f272,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(resolution,[],[f69,f214])).

fof(f214,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f212])).

fof(f215,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f205,f73,f212])).

fof(f205,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f64,f75])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f95,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f61,f82,f92])).

fof(f61,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f25,f57])).

fof(f25,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f90,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f60,f87,f78])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f26,f57])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f59,f82,f78])).

fof(f59,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f27,f57,f57])).

fof(f27,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f58,f73])).

fof(f58,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f28,f57,f55])).

fof(f28,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.51  % (12232)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (12247)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (12239)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (12224)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (12239)Refutation not found, incomplete strategy% (12239)------------------------------
% 0.20/0.52  % (12239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12239)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12239)Memory used [KB]: 6140
% 0.20/0.52  % (12239)Time elapsed: 0.003 s
% 0.20/0.52  % (12239)------------------------------
% 0.20/0.52  % (12239)------------------------------
% 0.20/0.52  % (12231)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (12229)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (12225)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (12248)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (12251)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (12230)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (12240)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (12228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (12227)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (12234)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (12246)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (12234)Refutation not found, incomplete strategy% (12234)------------------------------
% 0.20/0.54  % (12234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12234)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12234)Memory used [KB]: 10618
% 0.20/0.54  % (12234)Time elapsed: 0.122 s
% 0.20/0.54  % (12234)------------------------------
% 0.20/0.54  % (12234)------------------------------
% 0.20/0.54  % (12233)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (12253)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (12245)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (12243)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (12244)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (12242)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (12238)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (12237)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (12235)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (12235)Refutation not found, incomplete strategy% (12235)------------------------------
% 0.20/0.55  % (12235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12235)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12235)Memory used [KB]: 10618
% 0.20/0.55  % (12235)Time elapsed: 0.137 s
% 0.20/0.55  % (12235)------------------------------
% 0.20/0.55  % (12235)------------------------------
% 0.20/0.55  % (12236)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (12252)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (12226)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.57  % (12250)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.58  % (12241)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.61/0.59  % (12241)Refutation not found, incomplete strategy% (12241)------------------------------
% 1.61/0.59  % (12241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (12240)Refutation found. Thanks to Tanya!
% 1.77/0.59  % SZS status Theorem for theBenchmark
% 1.77/0.59  % SZS output start Proof for theBenchmark
% 1.77/0.59  fof(f764,plain,(
% 1.77/0.59    $false),
% 1.77/0.59    inference(avatar_sat_refutation,[],[f76,f85,f90,f95,f215,f273,f325,f711,f721,f741,f757,f763])).
% 1.77/0.59  fof(f763,plain,(
% 1.77/0.59    spl3_5 | spl3_10 | ~spl3_3 | ~spl3_19),
% 1.77/0.59    inference(avatar_split_clause,[],[f762,f754,f82,f294,f92])).
% 1.77/0.59  fof(f92,plain,(
% 1.77/0.59    spl3_5 <=> k1_xboole_0 = sK2),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.77/0.59  fof(f294,plain,(
% 1.77/0.59    spl3_10 <=> sK1 = sK2),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.77/0.59  fof(f82,plain,(
% 1.77/0.59    spl3_3 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.77/0.59  fof(f754,plain,(
% 1.77/0.59    spl3_19 <=> r1_tarski(sK2,sK1)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.77/0.59  fof(f762,plain,(
% 1.77/0.59    sK1 = sK2 | k1_xboole_0 = sK2 | (~spl3_3 | ~spl3_19)),
% 1.77/0.59    inference(resolution,[],[f288,f756])).
% 1.77/0.59  fof(f756,plain,(
% 1.77/0.59    r1_tarski(sK2,sK1) | ~spl3_19),
% 1.77/0.59    inference(avatar_component_clause,[],[f754])).
% 1.77/0.59  fof(f288,plain,(
% 1.77/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl3_3),
% 1.77/0.59    inference(superposition,[],[f69,f83])).
% 1.77/0.59  fof(f83,plain,(
% 1.77/0.59    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_3),
% 1.77/0.59    inference(avatar_component_clause,[],[f82])).
% 1.77/0.59  fof(f69,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(definition_unfolding,[],[f41,f57,f57])).
% 1.77/0.59  fof(f57,plain,(
% 1.77/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f31,f54])).
% 1.77/0.59  fof(f54,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f38,f53])).
% 1.77/0.59  fof(f53,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f44,f52])).
% 1.77/0.59  fof(f52,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f46,f51])).
% 1.77/0.59  fof(f51,plain,(
% 1.77/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f47,f50])).
% 1.77/0.59  fof(f50,plain,(
% 1.77/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f48,f49])).
% 1.77/0.59  fof(f49,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f17])).
% 1.77/0.59  fof(f17,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.77/0.59  fof(f48,plain,(
% 1.77/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f16])).
% 1.77/0.59  fof(f16,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.77/0.59  fof(f47,plain,(
% 1.77/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f15])).
% 1.77/0.59  fof(f15,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.77/0.59  fof(f46,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f14])).
% 1.77/0.59  fof(f14,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.77/0.59  fof(f44,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f13])).
% 1.77/0.59  fof(f13,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.77/0.59  fof(f38,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f12])).
% 1.77/0.59  fof(f12,axiom,(
% 1.77/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.77/0.59  fof(f31,plain,(
% 1.77/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f11])).
% 1.77/0.59  fof(f11,axiom,(
% 1.77/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.77/0.59  fof(f41,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f18])).
% 1.77/0.59  fof(f18,axiom,(
% 1.77/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.77/0.59  fof(f757,plain,(
% 1.77/0.59    spl3_19 | ~spl3_17),
% 1.77/0.59    inference(avatar_split_clause,[],[f752,f738,f754])).
% 1.77/0.59  fof(f738,plain,(
% 1.77/0.59    spl3_17 <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.77/0.59  fof(f752,plain,(
% 1.77/0.59    r1_tarski(sK2,sK1) | ~spl3_17),
% 1.77/0.59    inference(forward_demodulation,[],[f744,f122])).
% 1.77/0.59  fof(f122,plain,(
% 1.77/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.77/0.59    inference(superposition,[],[f118,f36])).
% 1.77/0.59  fof(f36,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f1])).
% 1.77/0.59  fof(f1,axiom,(
% 1.77/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.77/0.59  fof(f118,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.77/0.59    inference(forward_demodulation,[],[f104,f96])).
% 1.77/0.59  fof(f96,plain,(
% 1.77/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.77/0.59    inference(superposition,[],[f36,f30])).
% 1.77/0.59  fof(f30,plain,(
% 1.77/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f5])).
% 1.77/0.59  fof(f5,axiom,(
% 1.77/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.77/0.59  fof(f104,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.77/0.59    inference(superposition,[],[f45,f29])).
% 1.77/0.59  fof(f29,plain,(
% 1.77/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f8])).
% 1.77/0.59  fof(f8,axiom,(
% 1.77/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.77/0.59  fof(f45,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f7])).
% 1.77/0.59  fof(f7,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.77/0.59  fof(f744,plain,(
% 1.77/0.59    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl3_17),
% 1.77/0.59    inference(superposition,[],[f193,f740])).
% 1.77/0.59  fof(f740,plain,(
% 1.77/0.59    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_17),
% 1.77/0.59    inference(avatar_component_clause,[],[f738])).
% 1.77/0.59  fof(f193,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 1.77/0.59    inference(forward_demodulation,[],[f65,f45])).
% 1.77/0.59  fof(f65,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f35,f56])).
% 1.77/0.59  fof(f56,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f39,f55])).
% 1.77/0.59  fof(f55,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f37,f54])).
% 1.77/0.59  fof(f37,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f19])).
% 1.77/0.59  fof(f19,axiom,(
% 1.77/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.77/0.59  fof(f39,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f10])).
% 1.77/0.59  fof(f10,axiom,(
% 1.77/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.77/0.59  fof(f35,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f4])).
% 1.77/0.59  fof(f4,axiom,(
% 1.77/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.77/0.59  fof(f741,plain,(
% 1.77/0.59    spl3_17 | ~spl3_1 | ~spl3_3),
% 1.77/0.59    inference(avatar_split_clause,[],[f736,f82,f73,f738])).
% 1.77/0.59  fof(f73,plain,(
% 1.77/0.59    spl3_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.77/0.59  fof(f736,plain,(
% 1.77/0.59    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (~spl3_1 | ~spl3_3)),
% 1.77/0.59    inference(forward_demodulation,[],[f75,f83])).
% 1.77/0.59  fof(f75,plain,(
% 1.77/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_1),
% 1.77/0.59    inference(avatar_component_clause,[],[f73])).
% 1.77/0.59  fof(f721,plain,(
% 1.77/0.59    ~spl3_10 | spl3_2 | ~spl3_3),
% 1.77/0.59    inference(avatar_split_clause,[],[f287,f82,f78,f294])).
% 1.77/0.59  fof(f78,plain,(
% 1.77/0.59    spl3_2 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.77/0.59  fof(f287,plain,(
% 1.77/0.59    sK1 != sK2 | (spl3_2 | ~spl3_3)),
% 1.77/0.59    inference(backward_demodulation,[],[f80,f83])).
% 1.77/0.59  fof(f80,plain,(
% 1.77/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_2),
% 1.77/0.59    inference(avatar_component_clause,[],[f78])).
% 1.77/0.59  fof(f711,plain,(
% 1.77/0.59    spl3_2 | ~spl3_8),
% 1.77/0.59    inference(avatar_split_clause,[],[f707,f278,f78])).
% 1.77/0.59  fof(f278,plain,(
% 1.77/0.59    spl3_8 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.77/0.59  fof(f707,plain,(
% 1.77/0.59    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_8),
% 1.77/0.59    inference(backward_demodulation,[],[f280,f631])).
% 1.77/0.59  fof(f631,plain,(
% 1.77/0.59    ( ! [X0] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.77/0.59    inference(forward_demodulation,[],[f630,f63])).
% 1.77/0.59  fof(f63,plain,(
% 1.77/0.59    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.77/0.59    inference(definition_unfolding,[],[f33,f55])).
% 1.77/0.59  fof(f33,plain,(
% 1.77/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f23])).
% 1.77/0.59  fof(f23,plain,(
% 1.77/0.59    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.77/0.59    inference(rectify,[],[f2])).
% 1.77/0.59  fof(f2,axiom,(
% 1.77/0.59    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.77/0.59  fof(f630,plain,(
% 1.77/0.59    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.77/0.59    inference(forward_demodulation,[],[f601,f118])).
% 1.77/0.59  fof(f601,plain,(
% 1.77/0.59    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))) )),
% 1.77/0.59    inference(superposition,[],[f505,f29])).
% 1.77/0.59  fof(f505,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))))) )),
% 1.77/0.59    inference(forward_demodulation,[],[f66,f45])).
% 1.77/0.59  fof(f66,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f40,f55,f55,f56])).
% 1.77/0.59  fof(f40,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f9])).
% 1.77/0.59  fof(f9,axiom,(
% 1.77/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 1.77/0.59  fof(f280,plain,(
% 1.77/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl3_8),
% 1.77/0.59    inference(avatar_component_clause,[],[f278])).
% 1.77/0.59  fof(f325,plain,(
% 1.77/0.59    spl3_8 | ~spl3_1 | ~spl3_4),
% 1.77/0.59    inference(avatar_split_clause,[],[f324,f87,f73,f278])).
% 1.77/0.59  fof(f87,plain,(
% 1.77/0.59    spl3_4 <=> k1_xboole_0 = sK1),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.77/0.59  fof(f324,plain,(
% 1.77/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (~spl3_1 | ~spl3_4)),
% 1.77/0.59    inference(forward_demodulation,[],[f75,f88])).
% 1.77/0.59  fof(f88,plain,(
% 1.77/0.59    k1_xboole_0 = sK1 | ~spl3_4),
% 1.77/0.59    inference(avatar_component_clause,[],[f87])).
% 1.77/0.59  fof(f273,plain,(
% 1.77/0.59    spl3_4 | spl3_3 | ~spl3_7),
% 1.77/0.59    inference(avatar_split_clause,[],[f272,f212,f82,f87])).
% 1.77/0.59  fof(f212,plain,(
% 1.77/0.59    spl3_7 <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.77/0.59  fof(f272,plain,(
% 1.77/0.59    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | ~spl3_7),
% 1.77/0.59    inference(resolution,[],[f69,f214])).
% 1.77/0.59  fof(f214,plain,(
% 1.77/0.59    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_7),
% 1.77/0.59    inference(avatar_component_clause,[],[f212])).
% 1.77/0.59  fof(f215,plain,(
% 1.77/0.59    spl3_7 | ~spl3_1),
% 1.77/0.59    inference(avatar_split_clause,[],[f205,f73,f212])).
% 1.77/0.59  fof(f205,plain,(
% 1.77/0.59    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_1),
% 1.77/0.59    inference(superposition,[],[f64,f75])).
% 1.77/0.59  fof(f64,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f34,f55])).
% 1.77/0.59  fof(f34,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f6])).
% 1.77/0.59  fof(f6,axiom,(
% 1.77/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.77/0.59  fof(f95,plain,(
% 1.77/0.59    ~spl3_5 | ~spl3_3),
% 1.77/0.59    inference(avatar_split_clause,[],[f61,f82,f92])).
% 1.77/0.59  fof(f61,plain,(
% 1.77/0.59    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.77/0.59    inference(definition_unfolding,[],[f25,f57])).
% 1.77/0.59  fof(f25,plain,(
% 1.77/0.59    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.77/0.59    inference(cnf_transformation,[],[f24])).
% 1.77/0.59  fof(f24,plain,(
% 1.77/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.77/0.59    inference(ennf_transformation,[],[f21])).
% 1.77/0.59  fof(f21,negated_conjecture,(
% 1.77/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.77/0.59    inference(negated_conjecture,[],[f20])).
% 1.77/0.59  fof(f20,conjecture,(
% 1.77/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.77/0.59  fof(f90,plain,(
% 1.77/0.59    ~spl3_2 | ~spl3_4),
% 1.77/0.59    inference(avatar_split_clause,[],[f60,f87,f78])).
% 1.77/0.59  fof(f60,plain,(
% 1.77/0.59    k1_xboole_0 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.77/0.59    inference(definition_unfolding,[],[f26,f57])).
% 1.77/0.59  fof(f26,plain,(
% 1.77/0.59    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.77/0.59    inference(cnf_transformation,[],[f24])).
% 1.77/0.59  fof(f85,plain,(
% 1.77/0.59    ~spl3_2 | ~spl3_3),
% 1.77/0.59    inference(avatar_split_clause,[],[f59,f82,f78])).
% 1.77/0.59  fof(f59,plain,(
% 1.77/0.59    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.77/0.59    inference(definition_unfolding,[],[f27,f57,f57])).
% 1.77/0.59  fof(f27,plain,(
% 1.77/0.59    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.77/0.59    inference(cnf_transformation,[],[f24])).
% 1.77/0.59  fof(f76,plain,(
% 1.77/0.59    spl3_1),
% 1.77/0.59    inference(avatar_split_clause,[],[f58,f73])).
% 1.77/0.59  fof(f58,plain,(
% 1.77/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.77/0.59    inference(definition_unfolding,[],[f28,f57,f55])).
% 1.77/0.59  fof(f28,plain,(
% 1.77/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.77/0.59    inference(cnf_transformation,[],[f24])).
% 1.77/0.59  % SZS output end Proof for theBenchmark
% 1.77/0.59  % (12240)------------------------------
% 1.77/0.59  % (12240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (12240)Termination reason: Refutation
% 1.77/0.59  
% 1.77/0.59  % (12240)Memory used [KB]: 11385
% 1.77/0.59  % (12240)Time elapsed: 0.157 s
% 1.77/0.59  % (12240)------------------------------
% 1.77/0.59  % (12240)------------------------------
% 1.77/0.59  % (12223)Success in time 0.231 s
%------------------------------------------------------------------------------
