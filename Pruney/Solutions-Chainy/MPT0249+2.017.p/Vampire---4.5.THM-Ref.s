%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:12 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 257 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  258 ( 501 expanded)
%              Number of equality atoms :  100 ( 277 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f111,f124,f131,f176,f281,f284,f384,f403,f405])).

fof(f405,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f403,plain,
    ( ~ spl3_7
    | spl3_9
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl3_7
    | spl3_9
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f383,f171,f395])).

fof(f395,plain,
    ( ! [X2] :
        ( r1_tarski(sK1,X2)
        | r1_xboole_0(sK1,X2) )
    | ~ spl3_7 ),
    inference(resolution,[],[f320,f318])).

fof(f318,plain,
    ( ! [X4] :
        ( r2_hidden(sK0,X4)
        | r1_xboole_0(sK1,X4) )
    | ~ spl3_7 ),
    inference(superposition,[],[f78,f123])).

fof(f123,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_7
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f320,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK0,X6)
        | r1_tarski(sK1,X6) )
    | ~ spl3_7 ),
    inference(superposition,[],[f76,f123])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f171,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_9
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f383,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl3_16
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f384,plain,
    ( ~ spl3_16
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f351,f121,f102,f97,f381])).

fof(f97,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( spl3_4
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f351,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f350,f228])).

fof(f228,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f227,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f227,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f83,f79])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f350,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f349,f141])).

fof(f141,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f349,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f348,f64])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f348,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f331,f123])).

fof(f331,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f276,f104])).

fof(f104,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f276,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f73,f63])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f284,plain,
    ( spl3_8
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl3_8
    | spl3_12 ),
    inference(unit_resulting_resolution,[],[f130,f280,f78])).

fof(f280,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_12
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f281,plain,
    ( ~ spl3_12
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f273,f108,f92,f278])).

fof(f92,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f108,plain,
    ( spl3_5
  <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f273,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f201,f110])).

fof(f110,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k1_xboole_0 = X1
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f43,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f176,plain,
    ( ~ spl3_9
    | spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f165,f102,f173,f169])).

fof(f173,plain,
    ( spl3_10
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f165,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f74,f104])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f131,plain,
    ( ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f125,f117,f128])).

fof(f117,plain,
    ( spl3_6
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f125,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_6 ),
    inference(resolution,[],[f76,f119])).

fof(f119,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f115,f108,f121,f117])).

fof(f115,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f61,f110])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f106,f102,f108])).

fof(f106,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f75,f104])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f105,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f71,f102])).

fof(f71,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f39,f70,f68])).

fof(f39,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f100,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f42,f97])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f92])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f87,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:15:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.53  % (11213)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (11206)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (11209)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (11208)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (11205)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.55  % (11210)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (11229)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (11218)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.55  % (11205)Refutation not found, incomplete strategy% (11205)------------------------------
% 1.39/0.55  % (11205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (11205)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (11205)Memory used [KB]: 1663
% 1.39/0.55  % (11205)Time elapsed: 0.089 s
% 1.39/0.55  % (11205)------------------------------
% 1.39/0.55  % (11205)------------------------------
% 1.39/0.55  % (11221)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.55  % (11224)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (11227)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.55  % (11219)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.56  % (11204)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.56  % (11225)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.56  % (11211)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.56  % (11222)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.56  % (11217)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.57  % (11228)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.57  % (11216)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.57  % (11221)Refutation not found, incomplete strategy% (11221)------------------------------
% 1.39/0.57  % (11221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (11223)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.57  % (11220)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.57  % (11221)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (11221)Memory used [KB]: 1791
% 1.39/0.57  % (11221)Time elapsed: 0.123 s
% 1.39/0.57  % (11221)------------------------------
% 1.39/0.57  % (11221)------------------------------
% 1.53/0.57  % (11232)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.53/0.57  % (11207)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.53/0.57  % (11220)Refutation not found, incomplete strategy% (11220)------------------------------
% 1.53/0.57  % (11220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (11212)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.53/0.57  % (11220)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (11220)Memory used [KB]: 10618
% 1.53/0.57  % (11220)Time elapsed: 0.144 s
% 1.53/0.57  % (11220)------------------------------
% 1.53/0.57  % (11220)------------------------------
% 1.53/0.57  % (11232)Refutation not found, incomplete strategy% (11232)------------------------------
% 1.53/0.57  % (11232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (11232)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (11232)Memory used [KB]: 10746
% 1.53/0.57  % (11232)Time elapsed: 0.145 s
% 1.53/0.57  % (11232)------------------------------
% 1.53/0.57  % (11232)------------------------------
% 1.53/0.57  % (11230)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.53/0.57  % (11226)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.53/0.57  % (11214)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.53/0.57  % (11216)Refutation not found, incomplete strategy% (11216)------------------------------
% 1.53/0.57  % (11216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (11216)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (11216)Memory used [KB]: 10618
% 1.53/0.57  % (11216)Time elapsed: 0.146 s
% 1.53/0.57  % (11216)------------------------------
% 1.53/0.57  % (11216)------------------------------
% 1.53/0.58  % (11214)Refutation not found, incomplete strategy% (11214)------------------------------
% 1.53/0.58  % (11214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (11214)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (11214)Memory used [KB]: 10746
% 1.53/0.58  % (11214)Time elapsed: 0.144 s
% 1.53/0.58  % (11214)------------------------------
% 1.53/0.58  % (11214)------------------------------
% 1.53/0.58  % (11233)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.53/0.58  % (11233)Refutation not found, incomplete strategy% (11233)------------------------------
% 1.53/0.58  % (11233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (11233)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (11233)Memory used [KB]: 1663
% 1.53/0.58  % (11233)Time elapsed: 0.154 s
% 1.53/0.58  % (11233)------------------------------
% 1.53/0.58  % (11233)------------------------------
% 1.53/0.59  % (11227)Refutation found. Thanks to Tanya!
% 1.53/0.59  % SZS status Theorem for theBenchmark
% 1.53/0.59  % SZS output start Proof for theBenchmark
% 1.53/0.59  fof(f406,plain,(
% 1.53/0.59    $false),
% 1.53/0.59    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f111,f124,f131,f176,f281,f284,f384,f403,f405])).
% 1.53/0.59  fof(f405,plain,(
% 1.53/0.59    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 = sK2),
% 1.53/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.59  fof(f403,plain,(
% 1.53/0.59    ~spl3_7 | spl3_9 | spl3_16),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f396])).
% 1.53/0.59  fof(f396,plain,(
% 1.53/0.59    $false | (~spl3_7 | spl3_9 | spl3_16)),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f383,f171,f395])).
% 1.53/0.59  fof(f395,plain,(
% 1.53/0.59    ( ! [X2] : (r1_tarski(sK1,X2) | r1_xboole_0(sK1,X2)) ) | ~spl3_7),
% 1.53/0.59    inference(resolution,[],[f320,f318])).
% 1.53/0.59  fof(f318,plain,(
% 1.53/0.59    ( ! [X4] : (r2_hidden(sK0,X4) | r1_xboole_0(sK1,X4)) ) | ~spl3_7),
% 1.53/0.59    inference(superposition,[],[f78,f123])).
% 1.53/0.59  fof(f123,plain,(
% 1.53/0.59    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_7),
% 1.53/0.59    inference(avatar_component_clause,[],[f121])).
% 1.53/0.59  fof(f121,plain,(
% 1.53/0.59    spl3_7 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.53/0.59  fof(f78,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f53,f70])).
% 1.53/0.59  fof(f70,plain,(
% 1.53/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f54,f67])).
% 1.53/0.59  fof(f67,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f65,f66])).
% 1.53/0.59  fof(f66,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f13])).
% 1.53/0.59  fof(f13,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.59  fof(f65,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f12])).
% 1.53/0.59  fof(f12,axiom,(
% 1.53/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.59  fof(f54,plain,(
% 1.53/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f11])).
% 1.53/0.59  fof(f11,axiom,(
% 1.53/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.59  fof(f53,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f30])).
% 1.53/0.59  fof(f30,plain,(
% 1.53/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.53/0.59    inference(ennf_transformation,[],[f18])).
% 1.53/0.59  fof(f18,axiom,(
% 1.53/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.53/0.59  fof(f320,plain,(
% 1.53/0.59    ( ! [X6] : (~r2_hidden(sK0,X6) | r1_tarski(sK1,X6)) ) | ~spl3_7),
% 1.53/0.59    inference(superposition,[],[f76,f123])).
% 1.53/0.59  fof(f76,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f52,f70])).
% 1.53/0.59  fof(f52,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f34])).
% 1.53/0.59  fof(f34,plain,(
% 1.53/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.53/0.59    inference(nnf_transformation,[],[f21])).
% 1.53/0.59  fof(f21,axiom,(
% 1.53/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 1.53/0.59  fof(f171,plain,(
% 1.53/0.59    ~r1_tarski(sK1,sK2) | spl3_9),
% 1.53/0.59    inference(avatar_component_clause,[],[f169])).
% 1.53/0.59  fof(f169,plain,(
% 1.53/0.59    spl3_9 <=> r1_tarski(sK1,sK2)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.53/0.59  fof(f383,plain,(
% 1.53/0.59    ~r1_xboole_0(sK1,sK2) | spl3_16),
% 1.53/0.59    inference(avatar_component_clause,[],[f381])).
% 1.53/0.59  fof(f381,plain,(
% 1.53/0.59    spl3_16 <=> r1_xboole_0(sK1,sK2)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.53/0.59  fof(f384,plain,(
% 1.53/0.59    ~spl3_16 | spl3_3 | ~spl3_4 | ~spl3_7),
% 1.53/0.59    inference(avatar_split_clause,[],[f351,f121,f102,f97,f381])).
% 1.53/0.59  fof(f97,plain,(
% 1.53/0.59    spl3_3 <=> k1_xboole_0 = sK2),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.53/0.59  fof(f102,plain,(
% 1.53/0.59    spl3_4 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.53/0.59  fof(f351,plain,(
% 1.53/0.59    k1_xboole_0 = sK2 | ~r1_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_7)),
% 1.53/0.59    inference(forward_demodulation,[],[f350,f228])).
% 1.53/0.59  fof(f228,plain,(
% 1.53/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.53/0.59    inference(forward_demodulation,[],[f227,f46])).
% 1.53/0.59  fof(f46,plain,(
% 1.53/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f9])).
% 1.53/0.59  fof(f9,axiom,(
% 1.53/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.53/0.59  fof(f227,plain,(
% 1.53/0.59    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 1.53/0.59    inference(forward_demodulation,[],[f83,f79])).
% 1.53/0.59  fof(f79,plain,(
% 1.53/0.59    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f55,f70])).
% 1.53/0.59  fof(f55,plain,(
% 1.53/0.59    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f20])).
% 1.53/0.59  fof(f20,axiom,(
% 1.53/0.59    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.53/0.59  fof(f83,plain,(
% 1.53/0.59    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0) )),
% 1.53/0.59    inference(definition_unfolding,[],[f62,f69])).
% 1.53/0.59  fof(f69,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.53/0.59    inference(definition_unfolding,[],[f48,f68])).
% 1.53/0.59  fof(f68,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.53/0.59    inference(definition_unfolding,[],[f49,f67])).
% 1.53/0.59  fof(f49,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f19])).
% 1.53/0.59  fof(f19,axiom,(
% 1.53/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.53/0.59  fof(f48,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f10])).
% 1.53/0.59  fof(f10,axiom,(
% 1.53/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.53/0.59  fof(f62,plain,(
% 1.53/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.59    inference(cnf_transformation,[],[f25])).
% 1.53/0.59  fof(f25,plain,(
% 1.53/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.59    inference(rectify,[],[f3])).
% 1.53/0.59  fof(f3,axiom,(
% 1.53/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.53/0.59  fof(f350,plain,(
% 1.53/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) | ~r1_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_7)),
% 1.53/0.59    inference(forward_demodulation,[],[f349,f141])).
% 1.53/0.59  fof(f141,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.53/0.59    inference(superposition,[],[f63,f46])).
% 1.53/0.59  fof(f63,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f8])).
% 1.53/0.59  fof(f8,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.53/0.59  fof(f349,plain,(
% 1.53/0.59    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_7)),
% 1.53/0.59    inference(forward_demodulation,[],[f348,f64])).
% 1.53/0.59  fof(f64,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f1])).
% 1.53/0.59  fof(f1,axiom,(
% 1.53/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.53/0.59  fof(f348,plain,(
% 1.53/0.59    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~r1_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_7)),
% 1.53/0.59    inference(forward_demodulation,[],[f331,f123])).
% 1.53/0.59  fof(f331,plain,(
% 1.53/0.59    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,sK2) | ~spl3_4),
% 1.53/0.59    inference(superposition,[],[f276,f104])).
% 1.53/0.59  fof(f104,plain,(
% 1.53/0.59    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl3_4),
% 1.53/0.59    inference(avatar_component_clause,[],[f102])).
% 1.53/0.59  fof(f276,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(forward_demodulation,[],[f73,f63])).
% 1.53/0.59  fof(f73,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f44,f69])).
% 1.53/0.59  fof(f44,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f33])).
% 1.53/0.59  fof(f33,plain,(
% 1.53/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.53/0.59    inference(nnf_transformation,[],[f2])).
% 1.53/0.59  fof(f2,axiom,(
% 1.53/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.53/0.59  fof(f284,plain,(
% 1.53/0.59    spl3_8 | spl3_12),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f282])).
% 1.53/0.59  fof(f282,plain,(
% 1.53/0.59    $false | (spl3_8 | spl3_12)),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f130,f280,f78])).
% 1.53/0.59  fof(f280,plain,(
% 1.53/0.59    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl3_12),
% 1.53/0.59    inference(avatar_component_clause,[],[f278])).
% 1.53/0.59  fof(f278,plain,(
% 1.53/0.59    spl3_12 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.53/0.59  fof(f130,plain,(
% 1.53/0.59    ~r2_hidden(sK0,sK1) | spl3_8),
% 1.53/0.59    inference(avatar_component_clause,[],[f128])).
% 1.53/0.59  fof(f128,plain,(
% 1.53/0.59    spl3_8 <=> r2_hidden(sK0,sK1)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.53/0.59  fof(f281,plain,(
% 1.53/0.59    ~spl3_12 | spl3_2 | ~spl3_5),
% 1.53/0.59    inference(avatar_split_clause,[],[f273,f108,f92,f278])).
% 1.53/0.59  fof(f92,plain,(
% 1.53/0.59    spl3_2 <=> k1_xboole_0 = sK1),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.53/0.59  fof(f108,plain,(
% 1.53/0.59    spl3_5 <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.53/0.59  fof(f273,plain,(
% 1.53/0.59    k1_xboole_0 = sK1 | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl3_5),
% 1.53/0.59    inference(resolution,[],[f201,f110])).
% 1.53/0.59  fof(f110,plain,(
% 1.53/0.59    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_5),
% 1.53/0.59    inference(avatar_component_clause,[],[f108])).
% 1.53/0.59  fof(f201,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_xboole_0 = X1 | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(resolution,[],[f43,f84])).
% 1.53/0.59  fof(f84,plain,(
% 1.53/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.59    inference(equality_resolution,[],[f60])).
% 1.53/0.59  fof(f60,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f38])).
% 1.53/0.59  fof(f38,plain,(
% 1.53/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.59    inference(flattening,[],[f37])).
% 1.53/0.59  fof(f37,plain,(
% 1.53/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.59    inference(nnf_transformation,[],[f4])).
% 1.53/0.59  fof(f4,axiom,(
% 1.53/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.59  fof(f43,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f28])).
% 1.53/0.59  fof(f28,plain,(
% 1.53/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.53/0.59    inference(flattening,[],[f27])).
% 1.53/0.59  fof(f27,plain,(
% 1.53/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.53/0.59    inference(ennf_transformation,[],[f6])).
% 1.53/0.59  fof(f6,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.53/0.59  fof(f176,plain,(
% 1.53/0.59    ~spl3_9 | spl3_10 | ~spl3_4),
% 1.53/0.59    inference(avatar_split_clause,[],[f165,f102,f173,f169])).
% 1.53/0.59  fof(f173,plain,(
% 1.53/0.59    spl3_10 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.53/0.59  fof(f165,plain,(
% 1.53/0.59    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl3_4),
% 1.53/0.59    inference(superposition,[],[f74,f104])).
% 1.53/0.59  fof(f74,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f47,f68])).
% 1.53/0.59  fof(f47,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f29])).
% 1.53/0.59  fof(f29,plain,(
% 1.53/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.53/0.59    inference(ennf_transformation,[],[f5])).
% 1.53/0.59  fof(f5,axiom,(
% 1.53/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.53/0.59  fof(f131,plain,(
% 1.53/0.59    ~spl3_8 | spl3_6),
% 1.53/0.59    inference(avatar_split_clause,[],[f125,f117,f128])).
% 1.53/0.59  fof(f117,plain,(
% 1.53/0.59    spl3_6 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.53/0.59  fof(f125,plain,(
% 1.53/0.59    ~r2_hidden(sK0,sK1) | spl3_6),
% 1.53/0.59    inference(resolution,[],[f76,f119])).
% 1.53/0.59  fof(f119,plain,(
% 1.53/0.59    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl3_6),
% 1.53/0.59    inference(avatar_component_clause,[],[f117])).
% 1.53/0.59  fof(f124,plain,(
% 1.53/0.59    ~spl3_6 | spl3_7 | ~spl3_5),
% 1.53/0.59    inference(avatar_split_clause,[],[f115,f108,f121,f117])).
% 1.53/0.59  fof(f115,plain,(
% 1.53/0.59    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl3_5),
% 1.53/0.59    inference(resolution,[],[f61,f110])).
% 1.53/0.59  fof(f61,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f38])).
% 1.53/0.59  fof(f111,plain,(
% 1.53/0.59    spl3_5 | ~spl3_4),
% 1.53/0.59    inference(avatar_split_clause,[],[f106,f102,f108])).
% 1.53/0.59  fof(f106,plain,(
% 1.53/0.59    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_4),
% 1.53/0.59    inference(superposition,[],[f75,f104])).
% 1.53/0.59  fof(f75,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.53/0.59    inference(definition_unfolding,[],[f50,f68])).
% 1.53/0.59  fof(f50,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f7])).
% 1.53/0.59  fof(f7,axiom,(
% 1.53/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.53/0.59  fof(f105,plain,(
% 1.53/0.59    spl3_4),
% 1.53/0.59    inference(avatar_split_clause,[],[f71,f102])).
% 1.53/0.59  fof(f71,plain,(
% 1.53/0.59    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.53/0.59    inference(definition_unfolding,[],[f39,f70,f68])).
% 1.53/0.59  fof(f39,plain,(
% 1.53/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.53/0.59    inference(cnf_transformation,[],[f32])).
% 1.53/0.59  fof(f32,plain,(
% 1.53/0.59    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.53/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).
% 1.53/0.59  fof(f31,plain,(
% 1.53/0.59    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.53/0.59    introduced(choice_axiom,[])).
% 1.53/0.59  fof(f26,plain,(
% 1.53/0.59    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.53/0.59    inference(ennf_transformation,[],[f24])).
% 1.53/0.59  fof(f24,negated_conjecture,(
% 1.53/0.59    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.53/0.59    inference(negated_conjecture,[],[f23])).
% 1.53/0.59  fof(f23,conjecture,(
% 1.53/0.59    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.53/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.53/0.59  fof(f100,plain,(
% 1.53/0.59    ~spl3_3),
% 1.53/0.59    inference(avatar_split_clause,[],[f42,f97])).
% 1.53/0.59  fof(f42,plain,(
% 1.53/0.59    k1_xboole_0 != sK2),
% 1.53/0.59    inference(cnf_transformation,[],[f32])).
% 1.53/0.59  fof(f95,plain,(
% 1.53/0.59    ~spl3_2),
% 1.53/0.59    inference(avatar_split_clause,[],[f41,f92])).
% 1.53/0.59  fof(f41,plain,(
% 1.53/0.59    k1_xboole_0 != sK1),
% 1.53/0.59    inference(cnf_transformation,[],[f32])).
% 1.53/0.59  fof(f90,plain,(
% 1.53/0.59    ~spl3_1),
% 1.53/0.59    inference(avatar_split_clause,[],[f40,f87])).
% 1.53/0.59  fof(f87,plain,(
% 1.53/0.59    spl3_1 <=> sK1 = sK2),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.53/0.59  fof(f40,plain,(
% 1.53/0.59    sK1 != sK2),
% 1.53/0.59    inference(cnf_transformation,[],[f32])).
% 1.53/0.59  % SZS output end Proof for theBenchmark
% 1.53/0.59  % (11227)------------------------------
% 1.53/0.59  % (11227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (11227)Termination reason: Refutation
% 1.53/0.59  
% 1.53/0.59  % (11227)Memory used [KB]: 11001
% 1.53/0.59  % (11227)Time elapsed: 0.129 s
% 1.53/0.59  % (11227)------------------------------
% 1.53/0.59  % (11227)------------------------------
% 1.53/0.60  % (11203)Success in time 0.221 s
%------------------------------------------------------------------------------
