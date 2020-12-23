%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:48 EST 2020

% Result     : Theorem 4.36s
% Output     : Refutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 225 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 374 expanded)
%              Number of equality atoms :   88 ( 203 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7837,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f116,f137,f2081,f2092,f5780,f5938,f7640,f7836])).

fof(f7836,plain,
    ( spl3_28
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(avatar_contradiction_clause,[],[f7790])).

fof(f7790,plain,
    ( $false
    | spl3_28
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(unit_resulting_resolution,[],[f2091,f91,f5937,f7645])).

fof(f7645,plain,
    ( ! [X6,X7] :
        ( ~ r1_xboole_0(sK0,k5_xboole_0(X6,X7))
        | r2_hidden(sK1,X6)
        | ~ r2_hidden(sK1,X7) )
    | ~ spl3_59 ),
    inference(resolution,[],[f7639,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f7639,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f7638])).

fof(f7638,plain,
    ( spl3_59
  <=> ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f5937,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f5935])).

fof(f5935,plain,
    ( spl3_54
  <=> r1_xboole_0(sK0,k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f91,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f2091,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl3_28
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f7640,plain,
    ( spl3_59
    | spl3_1
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f7627,f5675,f113,f98,f7638])).

fof(f98,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( spl3_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f5675,plain,
    ( spl3_49
  <=> sK0 = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f7627,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_hidden(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) )
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f7547,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f7547,plain,
    ( ! [X0] :
        ( sK0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
        | ~ r2_hidden(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) )
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(superposition,[],[f7535,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f7535,plain,
    ( ! [X0] :
        ( sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(resolution,[],[f6077,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f70])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f6077,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)
        | sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) )
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f6076,f32])).

fof(f6076,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) )
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f5984,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f5984,plain,
    ( ! [X0] :
        ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))
        | ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) )
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(superposition,[],[f5813,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5813,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))))
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(backward_demodulation,[],[f628,f5676])).

fof(f5676,plain,
    ( sK0 = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f5675])).

fof(f628,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))))
    | ~ spl3_3 ),
    inference(superposition,[],[f128,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f50,f37,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f128,plain,
    ( ! [X4] : k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X4)) = k5_xboole_0(k1_xboole_0,X4)
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f5938,plain,
    ( spl3_54
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f5871,f5675,f5935])).

fof(f5871,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl3_49 ),
    inference(superposition,[],[f35,f5676])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f5780,plain,
    ( ~ spl3_4
    | spl3_49 ),
    inference(avatar_contradiction_clause,[],[f5771])).

fof(f5771,plain,
    ( $false
    | ~ spl3_4
    | spl3_49 ),
    inference(unit_resulting_resolution,[],[f136,f5677,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f5677,plain,
    ( sK0 != k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f5675])).

fof(f136,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2092,plain,
    ( ~ spl3_28
    | spl3_27 ),
    inference(avatar_split_clause,[],[f2082,f2078,f2089])).

fof(f2078,plain,
    ( spl3_27
  <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f2082,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_27 ),
    inference(resolution,[],[f2080,f76])).

fof(f2080,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f2078])).

fof(f2081,plain,
    ( spl3_2
    | ~ spl3_27
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f138,f134,f2078,f103])).

fof(f103,plain,
    ( spl3_2
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f138,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f136,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f137,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f130,f113,f134])).

fof(f130,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f77,f115])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f116,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f74,f113])).

fof(f74,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f28,f37,f72])).

fof(f28,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f106,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f73,f103])).

fof(f73,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f30,f72])).

fof(f30,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f98])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:32:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (14644)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (14643)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (14642)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (14661)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (14640)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (14668)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (14665)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (14656)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (14645)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (14667)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (14646)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14654)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (14641)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (14650)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (14664)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (14653)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (14660)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (14652)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (14658)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (14669)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (14670)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (14663)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (14670)Refutation not found, incomplete strategy% (14670)------------------------------
% 0.22/0.54  % (14670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14670)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14670)Memory used [KB]: 1663
% 0.22/0.54  % (14670)Time elapsed: 0.129 s
% 0.22/0.54  % (14670)------------------------------
% 0.22/0.54  % (14670)------------------------------
% 0.22/0.54  % (14666)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (14651)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (14657)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (14657)Refutation not found, incomplete strategy% (14657)------------------------------
% 0.22/0.55  % (14657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14657)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14657)Memory used [KB]: 10618
% 0.22/0.55  % (14657)Time elapsed: 0.139 s
% 0.22/0.55  % (14657)------------------------------
% 0.22/0.55  % (14657)------------------------------
% 0.22/0.55  % (14648)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (14659)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (14647)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (14662)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (14649)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.09/0.66  % (14643)Refutation not found, incomplete strategy% (14643)------------------------------
% 2.09/0.66  % (14643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.67  % (14643)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.67  
% 2.09/0.67  % (14643)Memory used [KB]: 6140
% 2.09/0.67  % (14643)Time elapsed: 0.249 s
% 2.09/0.67  % (14643)------------------------------
% 2.09/0.67  % (14643)------------------------------
% 2.09/0.68  % (14690)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.09/0.72  % (14691)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.34/0.81  % (14697)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.34/0.82  % (14642)Time limit reached!
% 3.34/0.82  % (14642)------------------------------
% 3.34/0.82  % (14642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.84  % (14642)Termination reason: Time limit
% 3.34/0.84  
% 3.34/0.84  % (14642)Memory used [KB]: 6524
% 3.34/0.84  % (14642)Time elapsed: 0.409 s
% 3.34/0.84  % (14642)------------------------------
% 3.34/0.84  % (14642)------------------------------
% 3.91/0.87  % (14665)Time limit reached!
% 3.91/0.87  % (14665)------------------------------
% 3.91/0.87  % (14665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.87  % (14665)Termination reason: Time limit
% 3.91/0.87  
% 3.91/0.87  % (14665)Memory used [KB]: 15607
% 3.91/0.87  % (14665)Time elapsed: 0.403 s
% 3.91/0.87  % (14665)------------------------------
% 3.91/0.87  % (14665)------------------------------
% 4.18/0.91  % (14654)Time limit reached!
% 4.18/0.91  % (14654)------------------------------
% 4.18/0.91  % (14654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.91  % (14654)Termination reason: Time limit
% 4.18/0.91  % (14654)Termination phase: Saturation
% 4.18/0.91  
% 4.18/0.91  % (14654)Memory used [KB]: 4733
% 4.18/0.91  % (14654)Time elapsed: 0.500 s
% 4.18/0.91  % (14654)------------------------------
% 4.18/0.91  % (14654)------------------------------
% 4.36/0.97  % (14704)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.36/0.99  % (14669)Refutation found. Thanks to Tanya!
% 4.36/0.99  % SZS status Theorem for theBenchmark
% 4.36/1.00  % (14646)Time limit reached!
% 4.36/1.00  % (14646)------------------------------
% 4.36/1.00  % (14646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/1.00  % (14646)Termination reason: Time limit
% 4.36/1.00  
% 4.36/1.00  % (14646)Memory used [KB]: 16886
% 4.36/1.00  % (14646)Time elapsed: 0.536 s
% 4.36/1.00  % (14646)------------------------------
% 4.36/1.00  % (14646)------------------------------
% 4.36/1.01  % SZS output start Proof for theBenchmark
% 4.36/1.01  fof(f7837,plain,(
% 4.36/1.01    $false),
% 4.36/1.01    inference(avatar_sat_refutation,[],[f101,f106,f116,f137,f2081,f2092,f5780,f5938,f7640,f7836])).
% 4.36/1.01  fof(f7836,plain,(
% 4.36/1.01    spl3_28 | ~spl3_54 | ~spl3_59),
% 4.36/1.01    inference(avatar_contradiction_clause,[],[f7790])).
% 4.36/1.01  fof(f7790,plain,(
% 4.36/1.01    $false | (spl3_28 | ~spl3_54 | ~spl3_59)),
% 4.36/1.01    inference(unit_resulting_resolution,[],[f2091,f91,f5937,f7645])).
% 4.36/1.01  fof(f7645,plain,(
% 4.36/1.01    ( ! [X6,X7] : (~r1_xboole_0(sK0,k5_xboole_0(X6,X7)) | r2_hidden(sK1,X6) | ~r2_hidden(sK1,X7)) ) | ~spl3_59),
% 4.36/1.01    inference(resolution,[],[f7639,f53])).
% 4.36/1.01  fof(f53,plain,(
% 4.36/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f26])).
% 4.36/1.01  fof(f26,plain,(
% 4.36/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.36/1.01    inference(ennf_transformation,[],[f3])).
% 4.36/1.01  fof(f3,axiom,(
% 4.36/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 4.36/1.01  fof(f7639,plain,(
% 4.36/1.01    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r1_xboole_0(sK0,X0)) ) | ~spl3_59),
% 4.36/1.01    inference(avatar_component_clause,[],[f7638])).
% 4.36/1.01  fof(f7638,plain,(
% 4.36/1.01    spl3_59 <=> ! [X0] : (~r2_hidden(sK1,X0) | ~r1_xboole_0(sK0,X0))),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 4.36/1.01  fof(f5937,plain,(
% 4.36/1.01    r1_xboole_0(sK0,k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl3_54),
% 4.36/1.01    inference(avatar_component_clause,[],[f5935])).
% 4.36/1.01  fof(f5935,plain,(
% 4.36/1.01    spl3_54 <=> r1_xboole_0(sK0,k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 4.36/1.01  fof(f91,plain,(
% 4.36/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4))) )),
% 4.36/1.01    inference(equality_resolution,[],[f90])).
% 4.36/1.01  fof(f90,plain,(
% 4.36/1.01    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3) )),
% 4.36/1.01    inference(equality_resolution,[],[f80])).
% 4.36/1.01  fof(f80,plain,(
% 4.36/1.01    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 4.36/1.01    inference(definition_unfolding,[],[f63,f70])).
% 4.36/1.01  fof(f70,plain,(
% 4.36/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f48,f69])).
% 4.36/1.01  fof(f69,plain,(
% 4.36/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f55,f68])).
% 4.36/1.01  fof(f68,plain,(
% 4.36/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f64,f67])).
% 4.36/1.01  fof(f67,plain,(
% 4.36/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f65,f66])).
% 4.36/1.01  fof(f66,plain,(
% 4.36/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f20])).
% 4.36/1.01  fof(f20,axiom,(
% 4.36/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 4.36/1.01  fof(f65,plain,(
% 4.36/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f19])).
% 4.36/1.01  fof(f19,axiom,(
% 4.36/1.01    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 4.36/1.01  fof(f64,plain,(
% 4.36/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f18])).
% 4.36/1.01  fof(f18,axiom,(
% 4.36/1.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.36/1.01  fof(f55,plain,(
% 4.36/1.01    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f17])).
% 4.36/1.01  fof(f17,axiom,(
% 4.36/1.01    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.36/1.01  fof(f48,plain,(
% 4.36/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f16])).
% 4.36/1.01  fof(f16,axiom,(
% 4.36/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.36/1.01  fof(f63,plain,(
% 4.36/1.01    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.36/1.01    inference(cnf_transformation,[],[f27])).
% 4.36/1.01  fof(f27,plain,(
% 4.36/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.36/1.01    inference(ennf_transformation,[],[f13])).
% 4.36/1.01  fof(f13,axiom,(
% 4.36/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 4.36/1.01  fof(f2091,plain,(
% 4.36/1.01    ~r2_hidden(sK1,sK0) | spl3_28),
% 4.36/1.01    inference(avatar_component_clause,[],[f2089])).
% 4.36/1.01  fof(f2089,plain,(
% 4.36/1.01    spl3_28 <=> r2_hidden(sK1,sK0)),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 4.36/1.01  fof(f7640,plain,(
% 4.36/1.01    spl3_59 | spl3_1 | ~spl3_3 | ~spl3_49),
% 4.36/1.01    inference(avatar_split_clause,[],[f7627,f5675,f113,f98,f7638])).
% 4.36/1.01  fof(f98,plain,(
% 4.36/1.01    spl3_1 <=> k1_xboole_0 = sK0),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.36/1.01  fof(f113,plain,(
% 4.36/1.01    spl3_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.36/1.01  fof(f5675,plain,(
% 4.36/1.01    spl3_49 <=> sK0 = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 4.36/1.01  fof(f7627,plain,(
% 4.36/1.01    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(sK1,X0) | ~r1_xboole_0(sK0,X0)) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(forward_demodulation,[],[f7547,f32])).
% 4.36/1.01  fof(f32,plain,(
% 4.36/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.36/1.01    inference(cnf_transformation,[],[f11])).
% 4.36/1.01  fof(f11,axiom,(
% 4.36/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 4.36/1.01  fof(f7547,plain,(
% 4.36/1.01    ( ! [X0] : (sK0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK1,X0) | ~r1_xboole_0(sK0,X0)) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(superposition,[],[f7535,f43])).
% 4.36/1.01  fof(f43,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f2])).
% 4.36/1.01  fof(f2,axiom,(
% 4.36/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 4.36/1.01  fof(f7535,plain,(
% 4.36/1.01    ( ! [X0] : (sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | ~r2_hidden(sK1,X0)) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(resolution,[],[f6077,f76])).
% 4.36/1.01  fof(f76,plain,(
% 4.36/1.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f44,f72])).
% 4.36/1.01  fof(f72,plain,(
% 4.36/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f33,f71])).
% 4.36/1.01  fof(f71,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f36,f70])).
% 4.36/1.01  fof(f36,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f15])).
% 4.36/1.01  fof(f15,axiom,(
% 4.36/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.36/1.01  fof(f33,plain,(
% 4.36/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f14])).
% 4.36/1.01  fof(f14,axiom,(
% 4.36/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.36/1.01  fof(f44,plain,(
% 4.36/1.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f21])).
% 4.36/1.01  fof(f21,axiom,(
% 4.36/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 4.36/1.01  fof(f6077,plain,(
% 4.36/1.01    ( ! [X0] : (~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) | sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(forward_demodulation,[],[f6076,f32])).
% 4.36/1.01  fof(f6076,plain,(
% 4.36/1.01    ( ! [X0] : (k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(forward_demodulation,[],[f5984,f31])).
% 4.36/1.01  fof(f31,plain,(
% 4.36/1.01    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f9])).
% 4.36/1.01  fof(f9,axiom,(
% 4.36/1.01    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 4.36/1.01  fof(f5984,plain,(
% 4.36/1.01    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) | ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(superposition,[],[f5813,f78])).
% 4.36/1.01  fof(f78,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f46,f37])).
% 4.36/1.01  fof(f37,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.36/1.01    inference(cnf_transformation,[],[f7])).
% 4.36/1.01  fof(f7,axiom,(
% 4.36/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.36/1.01  fof(f46,plain,(
% 4.36/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f5])).
% 4.36/1.01  fof(f5,axiom,(
% 4.36/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.36/1.01  fof(f5813,plain,(
% 4.36/1.01    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))))) ) | (~spl3_3 | ~spl3_49)),
% 4.36/1.01    inference(backward_demodulation,[],[f628,f5676])).
% 4.36/1.01  fof(f5676,plain,(
% 4.36/1.01    sK0 = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_49),
% 4.36/1.01    inference(avatar_component_clause,[],[f5675])).
% 4.36/1.01  fof(f628,plain,(
% 4.36/1.01    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))))) ) | ~spl3_3),
% 4.36/1.01    inference(superposition,[],[f128,f79])).
% 4.36/1.01  fof(f79,plain,(
% 4.36/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 4.36/1.01    inference(definition_unfolding,[],[f50,f37,f37])).
% 4.36/1.01  fof(f50,plain,(
% 4.36/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f10])).
% 4.36/1.01  fof(f10,axiom,(
% 4.36/1.01    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 4.36/1.01  fof(f128,plain,(
% 4.36/1.01    ( ! [X4] : (k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X4)) = k5_xboole_0(k1_xboole_0,X4)) ) | ~spl3_3),
% 4.36/1.01    inference(superposition,[],[f49,f115])).
% 4.36/1.01  fof(f115,plain,(
% 4.36/1.01    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl3_3),
% 4.36/1.01    inference(avatar_component_clause,[],[f113])).
% 4.36/1.01  fof(f49,plain,(
% 4.36/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.36/1.01    inference(cnf_transformation,[],[f12])).
% 4.36/1.01  fof(f12,axiom,(
% 4.36/1.01    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.36/1.01  fof(f5938,plain,(
% 4.36/1.01    spl3_54 | ~spl3_49),
% 4.36/1.01    inference(avatar_split_clause,[],[f5871,f5675,f5935])).
% 4.36/1.01  fof(f5871,plain,(
% 4.36/1.01    r1_xboole_0(sK0,k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl3_49),
% 4.36/1.01    inference(superposition,[],[f35,f5676])).
% 4.36/1.01  fof(f35,plain,(
% 4.36/1.01    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 4.36/1.01    inference(cnf_transformation,[],[f6])).
% 4.36/1.01  fof(f6,axiom,(
% 4.36/1.01    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 4.36/1.01  fof(f5780,plain,(
% 4.36/1.01    ~spl3_4 | spl3_49),
% 4.36/1.01    inference(avatar_contradiction_clause,[],[f5771])).
% 4.36/1.01  fof(f5771,plain,(
% 4.36/1.01    $false | (~spl3_4 | spl3_49)),
% 4.36/1.01    inference(unit_resulting_resolution,[],[f136,f5677,f38])).
% 4.36/1.01  fof(f38,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f25])).
% 4.36/1.01  fof(f25,plain,(
% 4.36/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.36/1.01    inference(ennf_transformation,[],[f8])).
% 4.36/1.01  fof(f8,axiom,(
% 4.36/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.36/1.01  fof(f5677,plain,(
% 4.36/1.01    sK0 != k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl3_49),
% 4.36/1.01    inference(avatar_component_clause,[],[f5675])).
% 4.36/1.01  fof(f136,plain,(
% 4.36/1.01    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_4),
% 4.36/1.01    inference(avatar_component_clause,[],[f134])).
% 4.36/1.01  fof(f134,plain,(
% 4.36/1.01    spl3_4 <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.36/1.01  fof(f2092,plain,(
% 4.36/1.01    ~spl3_28 | spl3_27),
% 4.36/1.01    inference(avatar_split_clause,[],[f2082,f2078,f2089])).
% 4.36/1.01  fof(f2078,plain,(
% 4.36/1.01    spl3_27 <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 4.36/1.01  fof(f2082,plain,(
% 4.36/1.01    ~r2_hidden(sK1,sK0) | spl3_27),
% 4.36/1.01    inference(resolution,[],[f2080,f76])).
% 4.36/1.01  fof(f2080,plain,(
% 4.36/1.01    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | spl3_27),
% 4.36/1.01    inference(avatar_component_clause,[],[f2078])).
% 4.36/1.01  fof(f2081,plain,(
% 4.36/1.01    spl3_2 | ~spl3_27 | ~spl3_4),
% 4.36/1.01    inference(avatar_split_clause,[],[f138,f134,f2078,f103])).
% 4.36/1.01  fof(f103,plain,(
% 4.36/1.01    spl3_2 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 4.36/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.36/1.01  fof(f138,plain,(
% 4.36/1.01    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_4),
% 4.36/1.01    inference(resolution,[],[f136,f41])).
% 4.36/1.01  fof(f41,plain,(
% 4.36/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 4.36/1.01    inference(cnf_transformation,[],[f4])).
% 4.36/1.01  fof(f4,axiom,(
% 4.36/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.36/1.01  fof(f137,plain,(
% 4.36/1.01    spl3_4 | ~spl3_3),
% 4.36/1.01    inference(avatar_split_clause,[],[f130,f113,f134])).
% 4.36/1.01  fof(f130,plain,(
% 4.36/1.01    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_3),
% 4.36/1.01    inference(trivial_inequality_removal,[],[f123])).
% 4.36/1.01  fof(f123,plain,(
% 4.36/1.01    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_3),
% 4.36/1.01    inference(superposition,[],[f77,f115])).
% 4.36/1.01  fof(f77,plain,(
% 4.36/1.01    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 4.36/1.01    inference(definition_unfolding,[],[f47,f37])).
% 4.36/1.01  fof(f47,plain,(
% 4.36/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 4.36/1.01    inference(cnf_transformation,[],[f5])).
% 4.36/1.01  fof(f116,plain,(
% 4.36/1.01    spl3_3),
% 4.36/1.01    inference(avatar_split_clause,[],[f74,f113])).
% 4.36/1.01  fof(f74,plain,(
% 4.36/1.01    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 4.36/1.01    inference(definition_unfolding,[],[f28,f37,f72])).
% 4.36/1.01  fof(f28,plain,(
% 4.36/1.01    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 4.36/1.01    inference(cnf_transformation,[],[f24])).
% 4.36/1.01  fof(f24,plain,(
% 4.36/1.01    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 4.36/1.01    inference(ennf_transformation,[],[f23])).
% 4.36/1.01  fof(f23,negated_conjecture,(
% 4.36/1.01    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 4.36/1.01    inference(negated_conjecture,[],[f22])).
% 4.36/1.01  fof(f22,conjecture,(
% 4.36/1.01    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 4.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 4.36/1.01  fof(f106,plain,(
% 4.36/1.01    ~spl3_2),
% 4.36/1.01    inference(avatar_split_clause,[],[f73,f103])).
% 4.36/1.01  fof(f73,plain,(
% 4.36/1.01    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 4.36/1.01    inference(definition_unfolding,[],[f30,f72])).
% 4.36/1.01  fof(f30,plain,(
% 4.36/1.01    sK0 != k1_tarski(sK1)),
% 4.36/1.01    inference(cnf_transformation,[],[f24])).
% 4.36/1.01  fof(f101,plain,(
% 4.36/1.01    ~spl3_1),
% 4.36/1.01    inference(avatar_split_clause,[],[f29,f98])).
% 4.36/1.01  fof(f29,plain,(
% 4.36/1.01    k1_xboole_0 != sK0),
% 4.36/1.01    inference(cnf_transformation,[],[f24])).
% 4.36/1.01  % SZS output end Proof for theBenchmark
% 4.36/1.01  % (14669)------------------------------
% 4.36/1.01  % (14669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/1.01  % (14669)Termination reason: Refutation
% 4.36/1.01  
% 4.36/1.01  % (14669)Memory used [KB]: 14711
% 4.36/1.01  % (14669)Time elapsed: 0.587 s
% 4.36/1.01  % (14669)------------------------------
% 4.36/1.01  % (14669)------------------------------
% 4.36/1.02  % (14635)Success in time 0.648 s
%------------------------------------------------------------------------------
