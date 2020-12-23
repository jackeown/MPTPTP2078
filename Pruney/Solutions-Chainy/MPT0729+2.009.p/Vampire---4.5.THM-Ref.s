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
% DateTime   : Thu Dec  3 12:55:11 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 795 expanded)
%              Number of leaves         :   26 ( 269 expanded)
%              Depth                    :   13
%              Number of atoms          :  212 ( 972 expanded)
%              Number of equality atoms :   45 ( 693 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f127,f139,f199,f219,f222,f262,f268,f301])).

fof(f301,plain,
    ( ~ spl2_1
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl2_1
    | spl2_9 ),
    inference(unit_resulting_resolution,[],[f297,f198,f87])).

fof(f87,plain,(
    ! [X4,X5] :
      ( r1_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5))
      | r2_hidden(X5,X4) ) ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,(
    ! [X4,X5] :
      ( X4 != X4
      | r1_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5))
      | r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f40,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f198,plain,
    ( ~ r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl2_9
  <=> r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f297,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f285,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f285,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f108,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f108,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_1
  <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f268,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f29,f122,f112,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f112,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f122,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f262,plain,(
    ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f76,f230,f81])).

fof(f81,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k5_enumset1(X4,X4,X4,X4,X4,X4,X4))
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f230,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_10 ),
    inference(superposition,[],[f61,f214])).

fof(f214,plain,
    ( sK0 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl2_10
  <=> sK0 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f61,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f30,f59])).

fof(f59,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f32,f57,f58])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f56])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f30,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f76,plain,(
    ! [X0] : r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f63,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f222,plain,
    ( spl2_9
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl2_9
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f200,f218,f64])).

fof(f218,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | spl2_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl2_11
  <=> r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f200,plain,
    ( r2_hidden(sK1,sK0)
    | spl2_9 ),
    inference(resolution,[],[f198,f87])).

fof(f219,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f202,f216,f120,f212])).

fof(f202,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f101,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0 ) ),
    inference(resolution,[],[f62,f39])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f57])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f101,plain,(
    ! [X2] :
      ( r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X2)
      | ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X2)
      | ~ r1_tarski(sK1,X2) ) ),
    inference(superposition,[],[f67,f60])).

fof(f60,plain,(
    k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f28,f59,f59])).

fof(f28,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f199,plain,
    ( spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f189,f196,f111])).

fof(f189,plain,
    ( ~ r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f100,f62])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
      | ~ r1_xboole_0(X1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | r1_tarski(X1,sK1) ) ),
    inference(superposition,[],[f68,f60])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f139,plain,
    ( spl2_1
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl2_1
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f115,f126,f87])).

fof(f126,plain,
    ( ~ r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_4
  <=> r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f115,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(resolution,[],[f109,f64])).

fof(f109,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f127,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f116,f124,f120])).

% (28835)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f116,plain,
    ( ~ r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f103,f68])).

fof(f103,plain,(
    r1_tarski(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f62,f60])).

fof(f114,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f104,f111,f107])).

fof(f104,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f98,f90])).

fof(f90,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X3)))
      | ~ r1_tarski(X5,X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f67,f46])).

fof(f98,plain,(
    r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f61,f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (28833)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.47  % (28846)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.52  % (28830)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.52  % (28839)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.53  % (28829)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.53  % (28852)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.53  % (28848)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.53  % (28840)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.22/0.53  % (28836)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.53  % (28844)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.53  % (28828)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (28827)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.53  % (28827)Refutation not found, incomplete strategy% (28827)------------------------------
% 1.33/0.53  % (28827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (28827)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (28827)Memory used [KB]: 1663
% 1.33/0.53  % (28827)Time elapsed: 0.118 s
% 1.33/0.53  % (28827)------------------------------
% 1.33/0.53  % (28827)------------------------------
% 1.33/0.53  % (28840)Refutation not found, incomplete strategy% (28840)------------------------------
% 1.33/0.53  % (28840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (28840)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (28840)Memory used [KB]: 1663
% 1.33/0.53  % (28840)Time elapsed: 0.083 s
% 1.33/0.53  % (28840)------------------------------
% 1.33/0.53  % (28840)------------------------------
% 1.33/0.53  % (28831)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (28826)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.54  % (28838)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.54  % (28854)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.54  % (28849)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.54  % (28847)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.54  % (28850)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.54  % (28845)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (28832)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (28851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (28837)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.55  % (28834)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.55  % (28842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.55  % (28842)Refutation not found, incomplete strategy% (28842)------------------------------
% 1.33/0.55  % (28842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (28842)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (28842)Memory used [KB]: 10618
% 1.33/0.55  % (28842)Time elapsed: 0.131 s
% 1.33/0.55  % (28842)------------------------------
% 1.33/0.55  % (28842)------------------------------
% 1.33/0.55  % (28841)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.55  % (28839)Refutation found. Thanks to Tanya!
% 1.33/0.55  % SZS status Theorem for theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f302,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(avatar_sat_refutation,[],[f114,f127,f139,f199,f219,f222,f262,f268,f301])).
% 1.33/0.55  fof(f301,plain,(
% 1.33/0.55    ~spl2_1 | spl2_9),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f299])).
% 1.33/0.55  fof(f299,plain,(
% 1.33/0.55    $false | (~spl2_1 | spl2_9)),
% 1.33/0.55    inference(unit_resulting_resolution,[],[f297,f198,f87])).
% 1.33/0.55  fof(f87,plain,(
% 1.33/0.55    ( ! [X4,X5] : (r1_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) | r2_hidden(X5,X4)) )),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f86])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    ( ! [X4,X5] : (X4 != X4 | r1_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) | r2_hidden(X5,X4)) )),
% 1.33/0.55    inference(superposition,[],[f40,f66])).
% 1.33/0.55  fof(f66,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f44,f58])).
% 1.33/0.55  fof(f58,plain,(
% 1.33/0.55    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f31,f56])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f35,f55])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f47,f54])).
% 1.33/0.55  fof(f54,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f50,f53])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f51,f52])).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f12])).
% 1.33/0.55  fof(f12,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f9])).
% 1.33/0.55  fof(f9,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f15])).
% 1.33/0.55  fof(f15,axiom,(
% 1.33/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.33/0.55  fof(f198,plain,(
% 1.33/0.55    ~r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl2_9),
% 1.33/0.55    inference(avatar_component_clause,[],[f196])).
% 1.33/0.55  fof(f196,plain,(
% 1.33/0.55    spl2_9 <=> r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.33/0.55  fof(f297,plain,(
% 1.33/0.55    ~r2_hidden(sK1,sK0) | ~spl2_1),
% 1.33/0.55    inference(resolution,[],[f285,f36])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.33/0.55  fof(f285,plain,(
% 1.33/0.55    r2_hidden(sK0,sK1) | ~spl2_1),
% 1.33/0.55    inference(resolution,[],[f108,f63])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f43,f58])).
% 1.33/0.55  fof(f43,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.33/0.55  fof(f108,plain,(
% 1.33/0.55    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl2_1),
% 1.33/0.55    inference(avatar_component_clause,[],[f107])).
% 1.33/0.55  fof(f107,plain,(
% 1.33/0.55    spl2_1 <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.33/0.55  fof(f268,plain,(
% 1.33/0.55    ~spl2_2 | ~spl2_3),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f264])).
% 1.33/0.55  fof(f264,plain,(
% 1.33/0.55    $false | (~spl2_2 | ~spl2_3)),
% 1.33/0.55    inference(unit_resulting_resolution,[],[f29,f122,f112,f39])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.55  fof(f112,plain,(
% 1.33/0.55    r1_tarski(sK0,sK1) | ~spl2_2),
% 1.33/0.55    inference(avatar_component_clause,[],[f111])).
% 1.33/0.55  fof(f111,plain,(
% 1.33/0.55    spl2_2 <=> r1_tarski(sK0,sK1)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.33/0.55  fof(f122,plain,(
% 1.33/0.55    r1_tarski(sK1,sK0) | ~spl2_3),
% 1.33/0.55    inference(avatar_component_clause,[],[f120])).
% 1.33/0.55  fof(f120,plain,(
% 1.33/0.55    spl2_3 <=> r1_tarski(sK1,sK0)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    sK0 != sK1),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.33/0.55    inference(negated_conjecture,[],[f19])).
% 1.33/0.55  fof(f19,conjecture,(
% 1.33/0.55    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).
% 1.33/0.55  fof(f262,plain,(
% 1.33/0.55    ~spl2_10),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f254])).
% 1.33/0.55  fof(f254,plain,(
% 1.33/0.55    $false | ~spl2_10),
% 1.33/0.55    inference(unit_resulting_resolution,[],[f76,f230,f81])).
% 1.33/0.55  fof(f81,plain,(
% 1.33/0.55    ( ! [X4,X5] : (~r2_hidden(X5,k5_enumset1(X4,X4,X4,X4,X4,X4,X4)) | ~r2_hidden(X4,X5)) )),
% 1.33/0.55    inference(resolution,[],[f64,f46])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f23])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,axiom,(
% 1.33/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f42,f58])).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f13])).
% 1.33/0.55  fof(f230,plain,(
% 1.33/0.55    r2_hidden(sK0,sK0) | ~spl2_10),
% 1.33/0.55    inference(superposition,[],[f61,f214])).
% 1.33/0.55  fof(f214,plain,(
% 1.33/0.55    sK0 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl2_10),
% 1.33/0.55    inference(avatar_component_clause,[],[f212])).
% 1.33/0.55  fof(f212,plain,(
% 1.33/0.55    spl2_10 <=> sK0 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    ( ! [X0] : (r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.33/0.55    inference(definition_unfolding,[],[f30,f59])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.33/0.55    inference(definition_unfolding,[],[f32,f57,f58])).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.33/0.55    inference(definition_unfolding,[],[f34,f56])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f14])).
% 1.33/0.55  fof(f14,axiom,(
% 1.33/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f16])).
% 1.33/0.55  fof(f16,axiom,(
% 1.33/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f17])).
% 1.33/0.55  fof(f17,axiom,(
% 1.33/0.55    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.33/0.55  fof(f76,plain,(
% 1.33/0.55    ( ! [X0] : (r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 1.33/0.55    inference(resolution,[],[f63,f69])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.55    inference(equality_resolution,[],[f38])).
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f2])).
% 1.33/0.55  fof(f222,plain,(
% 1.33/0.55    spl2_9 | spl2_11),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f220])).
% 1.33/0.55  fof(f220,plain,(
% 1.33/0.55    $false | (spl2_9 | spl2_11)),
% 1.33/0.55    inference(unit_resulting_resolution,[],[f200,f218,f64])).
% 1.33/0.55  fof(f218,plain,(
% 1.33/0.55    ~r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | spl2_11),
% 1.33/0.55    inference(avatar_component_clause,[],[f216])).
% 1.33/0.55  fof(f216,plain,(
% 1.33/0.55    spl2_11 <=> r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.33/0.55  fof(f200,plain,(
% 1.33/0.55    r2_hidden(sK1,sK0) | spl2_9),
% 1.33/0.55    inference(resolution,[],[f198,f87])).
% 1.33/0.55  fof(f219,plain,(
% 1.33/0.55    spl2_10 | ~spl2_3 | ~spl2_11),
% 1.33/0.55    inference(avatar_split_clause,[],[f202,f216,f120,f212])).
% 1.33/0.55  fof(f202,plain,(
% 1.33/0.55    ~r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~r1_tarski(sK1,sK0) | sK0 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.33/0.55    inference(resolution,[],[f101,f74])).
% 1.33/0.55  fof(f74,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0) )),
% 1.33/0.55    inference(resolution,[],[f62,f39])).
% 1.33/0.55  fof(f62,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.33/0.55    inference(definition_unfolding,[],[f33,f57])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.33/0.55  fof(f101,plain,(
% 1.33/0.55    ( ! [X2] : (r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X2) | ~r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X2) | ~r1_tarski(sK1,X2)) )),
% 1.33/0.55    inference(superposition,[],[f67,f60])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.33/0.55    inference(definition_unfolding,[],[f28,f59,f59])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f48,f57])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f25])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.33/0.55    inference(flattening,[],[f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.33/0.55  fof(f199,plain,(
% 1.33/0.55    spl2_2 | ~spl2_9),
% 1.33/0.55    inference(avatar_split_clause,[],[f189,f196,f111])).
% 1.33/0.55  fof(f189,plain,(
% 1.33/0.55    ~r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r1_tarski(sK0,sK1)),
% 1.33/0.55    inference(resolution,[],[f100,f62])).
% 1.33/0.55  fof(f100,plain,(
% 1.33/0.55    ( ! [X1] : (~r1_tarski(X1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r1_xboole_0(X1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r1_tarski(X1,sK1)) )),
% 1.33/0.55    inference(superposition,[],[f68,f60])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f49,f57])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.33/0.55    inference(flattening,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.33/0.55    inference(ennf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.33/0.55  fof(f139,plain,(
% 1.33/0.55    spl2_1 | spl2_4),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f137])).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    $false | (spl2_1 | spl2_4)),
% 1.33/0.55    inference(unit_resulting_resolution,[],[f115,f126,f87])).
% 1.33/0.55  fof(f126,plain,(
% 1.33/0.55    ~r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl2_4),
% 1.33/0.55    inference(avatar_component_clause,[],[f124])).
% 1.33/0.55  fof(f124,plain,(
% 1.33/0.55    spl2_4 <=> r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.33/0.55  fof(f115,plain,(
% 1.33/0.55    ~r2_hidden(sK0,sK1) | spl2_1),
% 1.33/0.55    inference(resolution,[],[f109,f64])).
% 1.33/0.55  fof(f109,plain,(
% 1.33/0.55    ~r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl2_1),
% 1.33/0.55    inference(avatar_component_clause,[],[f107])).
% 1.33/0.55  fof(f127,plain,(
% 1.33/0.55    spl2_3 | ~spl2_4),
% 1.33/0.55    inference(avatar_split_clause,[],[f116,f124,f120])).
% 1.33/0.55  % (28835)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.55  fof(f116,plain,(
% 1.33/0.55    ~r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r1_tarski(sK1,sK0)),
% 1.33/0.55    inference(resolution,[],[f103,f68])).
% 1.33/0.55  fof(f103,plain,(
% 1.33/0.55    r1_tarski(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.33/0.55    inference(superposition,[],[f62,f60])).
% 1.33/0.55  fof(f114,plain,(
% 1.33/0.55    ~spl2_1 | ~spl2_2),
% 1.33/0.55    inference(avatar_split_clause,[],[f104,f111,f107])).
% 1.33/0.55  fof(f104,plain,(
% 1.33/0.55    ~r1_tarski(sK0,sK1) | ~r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.33/0.55    inference(resolution,[],[f98,f90])).
% 1.33/0.55  fof(f90,plain,(
% 1.33/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X3))) | ~r1_tarski(X5,X4) | ~r1_tarski(X3,X4)) )),
% 1.33/0.55    inference(resolution,[],[f67,f46])).
% 1.33/0.55  fof(f98,plain,(
% 1.33/0.55    r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.33/0.55    inference(superposition,[],[f61,f60])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (28839)------------------------------
% 1.33/0.55  % (28839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (28839)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (28839)Memory used [KB]: 6396
% 1.33/0.55  % (28839)Time elapsed: 0.113 s
% 1.33/0.55  % (28839)------------------------------
% 1.33/0.55  % (28839)------------------------------
% 1.33/0.55  % (28825)Success in time 0.184 s
%------------------------------------------------------------------------------
