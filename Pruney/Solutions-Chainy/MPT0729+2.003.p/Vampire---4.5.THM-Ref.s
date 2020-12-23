%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:11 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 498 expanded)
%              Number of leaves         :   26 ( 173 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 665 expanded)
%              Number of equality atoms :   53 ( 406 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1902,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f220,f557,f628,f659,f1084,f1511,f1523,f1857,f1892,f1901])).

fof(f1901,plain,
    ( ~ spl2_4
    | spl2_86 ),
    inference(avatar_contradiction_clause,[],[f1895])).

fof(f1895,plain,
    ( $false
    | ~ spl2_4
    | spl2_86 ),
    inference(unit_resulting_resolution,[],[f1717,f1856,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1856,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl2_86 ),
    inference(avatar_component_clause,[],[f1854])).

fof(f1854,plain,
    ( spl2_86
  <=> r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f1717,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f1679,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1679,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f1562,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1562,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK0),X11)
        | r2_hidden(sK0,X11) )
    | ~ spl2_4 ),
    inference(superposition,[],[f63,f219])).

fof(f219,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl2_4
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1892,plain,(
    ~ spl2_85 ),
    inference(avatar_contradiction_clause,[],[f1883])).

fof(f1883,plain,
    ( $false
    | ~ spl2_85 ),
    inference(unit_resulting_resolution,[],[f67,f1852,f63])).

fof(f1852,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK1,sK0))
    | ~ spl2_85 ),
    inference(avatar_component_clause,[],[f1850])).

fof(f1850,plain,
    ( spl2_85
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f67,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1857,plain,
    ( spl2_85
    | ~ spl2_86
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1839,f217,f1854,f1850])).

fof(f1839,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK1,sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f1825,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | ~ r1_xboole_0(X2,X1)
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f61,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f49,f49])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1825,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK1,sK0))))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f190,f219])).

fof(f190,plain,(
    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f76,f53])).

fof(f53,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f27,f52,f52])).

fof(f52,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f30,f50,f51])).

fof(f30,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f27,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f76,plain,(
    ! [X12,X13] : r1_tarski(X12,k3_tarski(k2_enumset1(X13,X13,X13,X12))) ),
    inference(superposition,[],[f54,f55])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1523,plain,
    ( ~ spl2_28
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f1514])).

fof(f1514,plain,
    ( $false
    | ~ spl2_28
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f1512,f552,f63])).

fof(f552,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl2_28
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1512,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_30 ),
    inference(resolution,[],[f1501,f37])).

fof(f1501,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_30 ),
    inference(resolution,[],[f1395,f32])).

fof(f1395,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k4_xboole_0(sK0,sK1),X9)
        | r2_hidden(sK1,X9) )
    | ~ spl2_30 ),
    inference(superposition,[],[f63,f627])).

fof(f627,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl2_30
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1511,plain,
    ( spl2_29
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f1505])).

fof(f1505,plain,
    ( $false
    | spl2_29
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f67,f1466,f56])).

fof(f1466,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK0,sK1))
    | spl2_29
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f556,f627])).

fof(f556,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl2_29
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f1084,plain,
    ( spl2_5
    | ~ spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1080,f213,f231,f227])).

fof(f227,plain,
    ( spl2_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f231,plain,
    ( spl2_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f213,plain,
    ( spl2_3
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1080,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | sK0 = sK1
    | ~ spl2_3 ),
    inference(superposition,[],[f38,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f213])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f659,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f28,f229])).

fof(f229,plain,
    ( sK0 = sK1
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f227])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f628,plain,
    ( spl2_6
    | spl2_30 ),
    inference(avatar_split_clause,[],[f621,f625,f231])).

fof(f621,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f509,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f51,f51])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f509,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f186,f54])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))
      | r1_tarski(k4_xboole_0(X0,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f60,f53])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f557,plain,
    ( spl2_28
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f526,f554,f550])).

fof(f526,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f187,f76])).

fof(f187,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))
      | ~ r1_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1))
      | r1_tarski(X1,sK1) ) ),
    inference(superposition,[],[f61,f53])).

fof(f220,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f210,f217,f213])).

fof(f210,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0)
    | k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f198,f59])).

fof(f198,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f185,f60])).

fof(f185,plain,(
    r1_tarski(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f54,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (811794433)
% 0.13/0.36  ipcrm: permission denied for id (811827202)
% 0.13/0.37  ipcrm: permission denied for id (811892740)
% 0.13/0.37  ipcrm: permission denied for id (811925509)
% 0.13/0.37  ipcrm: permission denied for id (811958278)
% 0.13/0.37  ipcrm: permission denied for id (811991047)
% 0.13/0.37  ipcrm: permission denied for id (812089354)
% 0.13/0.37  ipcrm: permission denied for id (812122123)
% 0.13/0.38  ipcrm: permission denied for id (812285968)
% 0.13/0.38  ipcrm: permission denied for id (812351506)
% 0.13/0.38  ipcrm: permission denied for id (812384275)
% 0.13/0.39  ipcrm: permission denied for id (812417044)
% 0.13/0.39  ipcrm: permission denied for id (812449813)
% 0.13/0.39  ipcrm: permission denied for id (812482582)
% 0.13/0.39  ipcrm: permission denied for id (812515351)
% 0.13/0.39  ipcrm: permission denied for id (812580889)
% 0.13/0.39  ipcrm: permission denied for id (812613658)
% 0.13/0.40  ipcrm: permission denied for id (812646427)
% 0.13/0.40  ipcrm: permission denied for id (812679196)
% 0.13/0.40  ipcrm: permission denied for id (812711965)
% 0.13/0.40  ipcrm: permission denied for id (812744735)
% 0.13/0.40  ipcrm: permission denied for id (812777504)
% 0.13/0.40  ipcrm: permission denied for id (812810273)
% 0.13/0.41  ipcrm: permission denied for id (812843042)
% 0.13/0.41  ipcrm: permission denied for id (812908581)
% 0.13/0.41  ipcrm: permission denied for id (812941350)
% 0.13/0.41  ipcrm: permission denied for id (812974120)
% 0.13/0.41  ipcrm: permission denied for id (813006889)
% 0.20/0.42  ipcrm: permission denied for id (813236271)
% 0.20/0.42  ipcrm: permission denied for id (813301809)
% 0.20/0.42  ipcrm: permission denied for id (813367347)
% 0.20/0.43  ipcrm: permission denied for id (813432885)
% 0.20/0.43  ipcrm: permission denied for id (813498423)
% 0.20/0.43  ipcrm: permission denied for id (813531192)
% 0.20/0.43  ipcrm: permission denied for id (813563961)
% 0.20/0.44  ipcrm: permission denied for id (813727806)
% 0.20/0.44  ipcrm: permission denied for id (813858882)
% 0.20/0.44  ipcrm: permission denied for id (813891651)
% 0.20/0.45  ipcrm: permission denied for id (814055496)
% 0.20/0.45  ipcrm: permission denied for id (814153804)
% 0.20/0.45  ipcrm: permission denied for id (814252112)
% 0.20/0.45  ipcrm: permission denied for id (814284881)
% 0.20/0.46  ipcrm: permission denied for id (814317650)
% 0.20/0.46  ipcrm: permission denied for id (814383188)
% 0.20/0.46  ipcrm: permission denied for id (814415957)
% 0.20/0.46  ipcrm: permission denied for id (814547032)
% 0.20/0.46  ipcrm: permission denied for id (814579802)
% 0.20/0.47  ipcrm: permission denied for id (814612571)
% 0.20/0.47  ipcrm: permission denied for id (814743647)
% 0.20/0.48  ipcrm: permission denied for id (814940261)
% 0.20/0.48  ipcrm: permission denied for id (815136875)
% 0.20/0.48  ipcrm: permission denied for id (815169644)
% 0.20/0.48  ipcrm: permission denied for id (815202413)
% 0.20/0.48  ipcrm: permission denied for id (815235182)
% 0.20/0.49  ipcrm: permission denied for id (815300720)
% 0.20/0.49  ipcrm: permission denied for id (815333489)
% 0.20/0.49  ipcrm: permission denied for id (815497335)
% 0.20/0.49  ipcrm: permission denied for id (815530104)
% 0.20/0.50  ipcrm: permission denied for id (815595642)
% 0.78/0.60  % (7280)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.78/0.61  % (7281)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.78/0.62  % (7289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.78/0.62  % (7279)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.09/0.63  % (7295)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.09/0.64  % (7278)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.15/0.64  % (7279)Refutation not found, incomplete strategy% (7279)------------------------------
% 1.15/0.64  % (7279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.64  % (7279)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.64  
% 1.15/0.64  % (7279)Memory used [KB]: 1663
% 1.15/0.64  % (7279)Time elapsed: 0.102 s
% 1.15/0.64  % (7279)------------------------------
% 1.15/0.64  % (7279)------------------------------
% 1.15/0.65  % (7287)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.15/0.65  % (7303)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.15/0.65  % (7291)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.15/0.65  % (7294)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.15/0.66  % (7304)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.15/0.66  % (7296)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.15/0.66  % (7283)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.15/0.66  % (7304)Refutation not found, incomplete strategy% (7304)------------------------------
% 1.15/0.66  % (7304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.66  % (7304)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.66  
% 1.15/0.66  % (7304)Memory used [KB]: 6140
% 1.15/0.66  % (7304)Time elapsed: 0.059 s
% 1.15/0.66  % (7304)------------------------------
% 1.15/0.66  % (7304)------------------------------
% 1.15/0.66  % (7293)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.15/0.66  % (7296)Refutation not found, incomplete strategy% (7296)------------------------------
% 1.15/0.66  % (7296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.66  % (7296)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.66  
% 1.15/0.66  % (7296)Memory used [KB]: 1663
% 1.15/0.66  % (7296)Time elapsed: 0.070 s
% 1.15/0.66  % (7296)------------------------------
% 1.15/0.66  % (7296)------------------------------
% 1.15/0.66  % (7305)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.15/0.66  % (7288)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.15/0.66  % (7305)Refutation not found, incomplete strategy% (7305)------------------------------
% 1.15/0.66  % (7305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.66  % (7305)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.66  
% 1.15/0.66  % (7305)Memory used [KB]: 6140
% 1.15/0.66  % (7305)Time elapsed: 0.110 s
% 1.15/0.66  % (7305)------------------------------
% 1.15/0.66  % (7305)------------------------------
% 1.15/0.67  % (7300)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.15/0.67  % (7284)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.15/0.67  % (7307)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.15/0.67  % (7299)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.15/0.67  % (7286)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.15/0.67  % (7285)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.15/0.67  % (7294)Refutation not found, incomplete strategy% (7294)------------------------------
% 1.15/0.67  % (7294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.67  % (7294)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.67  
% 1.15/0.67  % (7294)Memory used [KB]: 10618
% 1.15/0.67  % (7294)Time elapsed: 0.129 s
% 1.15/0.67  % (7294)------------------------------
% 1.15/0.67  % (7294)------------------------------
% 1.15/0.68  % (7297)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.15/0.68  % (7307)Refutation not found, incomplete strategy% (7307)------------------------------
% 1.15/0.68  % (7307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.68  % (7307)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.68  
% 1.15/0.68  % (7307)Memory used [KB]: 1663
% 1.15/0.68  % (7307)Time elapsed: 0.003 s
% 1.15/0.68  % (7307)------------------------------
% 1.15/0.68  % (7307)------------------------------
% 1.15/0.68  % (7292)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.15/0.68  % (7301)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.15/0.69  % (7302)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.15/0.69  % (7282)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.15/0.69  % (7298)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.15/0.69  % (7292)Refutation not found, incomplete strategy% (7292)------------------------------
% 1.15/0.69  % (7292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.69  % (7292)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.69  
% 1.15/0.69  % (7292)Memory used [KB]: 1663
% 1.15/0.69  % (7292)Time elapsed: 0.144 s
% 1.15/0.69  % (7292)------------------------------
% 1.15/0.69  % (7292)------------------------------
% 1.15/0.69  % (7306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.15/0.71  % (7290)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.67/0.71  % (7290)Refutation not found, incomplete strategy% (7290)------------------------------
% 1.67/0.71  % (7290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.72  % (7290)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.72  
% 1.67/0.72  % (7290)Memory used [KB]: 10618
% 1.67/0.72  % (7290)Time elapsed: 0.150 s
% 1.67/0.72  % (7290)------------------------------
% 1.67/0.72  % (7290)------------------------------
% 1.67/0.73  % (7281)Refutation not found, incomplete strategy% (7281)------------------------------
% 1.67/0.73  % (7281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.73  % (7281)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.73  
% 1.67/0.73  % (7281)Memory used [KB]: 6140
% 1.67/0.73  % (7281)Time elapsed: 0.175 s
% 1.67/0.73  % (7281)------------------------------
% 1.67/0.73  % (7281)------------------------------
% 2.05/0.77  % (7313)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.05/0.78  % (7291)Refutation found. Thanks to Tanya!
% 2.05/0.78  % SZS status Theorem for theBenchmark
% 2.05/0.78  % (7278)Refutation not found, incomplete strategy% (7278)------------------------------
% 2.05/0.78  % (7278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.78  % (7278)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.78  
% 2.05/0.78  % (7278)Memory used [KB]: 1663
% 2.05/0.78  % (7278)Time elapsed: 0.238 s
% 2.05/0.78  % (7278)------------------------------
% 2.05/0.78  % (7278)------------------------------
% 2.05/0.79  % (7315)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.05/0.79  % (7315)Refutation not found, incomplete strategy% (7315)------------------------------
% 2.05/0.79  % (7315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.79  % (7315)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.79  
% 2.05/0.79  % (7315)Memory used [KB]: 6140
% 2.05/0.79  % (7315)Time elapsed: 0.099 s
% 2.05/0.79  % (7315)------------------------------
% 2.05/0.79  % (7315)------------------------------
% 2.05/0.79  % (7314)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.05/0.79  % (7293)Refutation not found, incomplete strategy% (7293)------------------------------
% 2.05/0.79  % (7293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.79  % (7293)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.79  
% 2.05/0.79  % (7293)Memory used [KB]: 6140
% 2.05/0.79  % (7293)Time elapsed: 0.229 s
% 2.05/0.79  % (7293)------------------------------
% 2.05/0.79  % (7293)------------------------------
% 2.05/0.80  % SZS output start Proof for theBenchmark
% 2.05/0.80  fof(f1902,plain,(
% 2.05/0.80    $false),
% 2.05/0.80    inference(avatar_sat_refutation,[],[f220,f557,f628,f659,f1084,f1511,f1523,f1857,f1892,f1901])).
% 2.05/0.80  fof(f1901,plain,(
% 2.05/0.80    ~spl2_4 | spl2_86),
% 2.05/0.80    inference(avatar_contradiction_clause,[],[f1895])).
% 2.05/0.80  fof(f1895,plain,(
% 2.05/0.80    $false | (~spl2_4 | spl2_86)),
% 2.05/0.80    inference(unit_resulting_resolution,[],[f1717,f1856,f56])).
% 2.05/0.80  fof(f56,plain,(
% 2.05/0.80    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f36,f51])).
% 2.05/0.80  fof(f51,plain,(
% 2.05/0.80    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f29,f49])).
% 2.05/0.80  fof(f49,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f35,f43])).
% 2.05/0.80  fof(f43,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f10])).
% 2.05/0.80  fof(f10,axiom,(
% 2.05/0.80    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.80  fof(f35,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f9])).
% 2.05/0.80  fof(f9,axiom,(
% 2.05/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.80  fof(f29,plain,(
% 2.05/0.80    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f8])).
% 2.05/0.80  fof(f8,axiom,(
% 2.05/0.80    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.05/0.80  fof(f36,plain,(
% 2.05/0.80    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f20])).
% 2.05/0.80  fof(f20,plain,(
% 2.05/0.80    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.05/0.80    inference(ennf_transformation,[],[f11])).
% 2.05/0.80  fof(f11,axiom,(
% 2.05/0.80    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.05/0.80  fof(f1856,plain,(
% 2.05/0.80    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl2_86),
% 2.05/0.80    inference(avatar_component_clause,[],[f1854])).
% 2.05/0.80  fof(f1854,plain,(
% 2.05/0.80    spl2_86 <=> r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 2.05/0.80  fof(f1717,plain,(
% 2.05/0.80    ~r2_hidden(sK1,sK0) | ~spl2_4),
% 2.05/0.80    inference(resolution,[],[f1679,f37])).
% 2.05/0.80  fof(f37,plain,(
% 2.05/0.80    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f21])).
% 2.05/0.80  fof(f21,plain,(
% 2.05/0.80    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.05/0.80    inference(ennf_transformation,[],[f1])).
% 2.05/0.80  fof(f1,axiom,(
% 2.05/0.80    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 2.05/0.80  fof(f1679,plain,(
% 2.05/0.80    r2_hidden(sK0,sK1) | ~spl2_4),
% 2.05/0.80    inference(resolution,[],[f1562,f32])).
% 2.05/0.80  fof(f32,plain,(
% 2.05/0.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f3])).
% 2.05/0.80  fof(f3,axiom,(
% 2.05/0.80    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.05/0.80  fof(f1562,plain,(
% 2.05/0.80    ( ! [X11] : (~r1_tarski(k4_xboole_0(sK1,sK0),X11) | r2_hidden(sK0,X11)) ) | ~spl2_4),
% 2.05/0.80    inference(superposition,[],[f63,f219])).
% 2.05/0.80  fof(f219,plain,(
% 2.05/0.80    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0) | ~spl2_4),
% 2.05/0.80    inference(avatar_component_clause,[],[f217])).
% 2.05/0.80  fof(f217,plain,(
% 2.05/0.80    spl2_4 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0)),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.05/0.80  fof(f63,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f47,f49])).
% 2.05/0.80  fof(f47,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f14])).
% 2.05/0.80  fof(f14,axiom,(
% 2.05/0.80    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.05/0.80  fof(f1892,plain,(
% 2.05/0.80    ~spl2_85),
% 2.05/0.80    inference(avatar_contradiction_clause,[],[f1883])).
% 2.05/0.80  fof(f1883,plain,(
% 2.05/0.80    $false | ~spl2_85),
% 2.05/0.80    inference(unit_resulting_resolution,[],[f67,f1852,f63])).
% 2.05/0.80  fof(f1852,plain,(
% 2.05/0.80    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK1,sK0)) | ~spl2_85),
% 2.05/0.80    inference(avatar_component_clause,[],[f1850])).
% 2.05/0.80  fof(f1850,plain,(
% 2.05/0.80    spl2_85 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK1,sK0))),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 2.05/0.80  fof(f67,plain,(
% 2.05/0.80    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.80    inference(resolution,[],[f42,f32])).
% 2.05/0.80  fof(f42,plain,(
% 2.05/0.80    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f23])).
% 2.05/0.80  fof(f23,plain,(
% 2.05/0.80    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.05/0.80    inference(ennf_transformation,[],[f16])).
% 2.05/0.80  fof(f16,axiom,(
% 2.05/0.80    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.05/0.80  fof(f1857,plain,(
% 2.05/0.80    spl2_85 | ~spl2_86 | ~spl2_4),
% 2.05/0.80    inference(avatar_split_clause,[],[f1839,f217,f1854,f1850])).
% 2.05/0.80  fof(f1839,plain,(
% 2.05/0.80    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK1,sK0)) | ~spl2_4),
% 2.05/0.80    inference(resolution,[],[f1825,f145])).
% 2.05/0.80  fof(f145,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k2_enumset1(X1,X1,X1,X0))) | ~r1_xboole_0(X2,X1) | r1_tarski(X2,X0)) )),
% 2.05/0.80    inference(superposition,[],[f61,f55])).
% 2.05/0.80  fof(f55,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f33,f49,f49])).
% 2.05/0.80  fof(f33,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f7])).
% 2.05/0.80  fof(f7,axiom,(
% 2.05/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.05/0.80  fof(f61,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f45,f50])).
% 2.05/0.80  fof(f50,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.05/0.80    inference(definition_unfolding,[],[f34,f49])).
% 2.05/0.80  fof(f34,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.05/0.80    inference(cnf_transformation,[],[f13])).
% 2.05/0.80  fof(f13,axiom,(
% 2.05/0.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.05/0.80  fof(f45,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f26])).
% 2.05/0.80  fof(f26,plain,(
% 2.05/0.80    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.05/0.80    inference(flattening,[],[f25])).
% 2.05/0.80  fof(f25,plain,(
% 2.05/0.80    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.05/0.80    inference(ennf_transformation,[],[f5])).
% 2.05/0.80  fof(f5,axiom,(
% 2.05/0.80    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.05/0.80  fof(f1825,plain,(
% 2.05/0.80    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK1,sK0)))) | ~spl2_4),
% 2.05/0.80    inference(forward_demodulation,[],[f190,f219])).
% 2.05/0.80  fof(f190,plain,(
% 2.05/0.80    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.05/0.80    inference(superposition,[],[f76,f53])).
% 2.05/0.80  fof(f53,plain,(
% 2.05/0.80    k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 2.05/0.80    inference(definition_unfolding,[],[f27,f52,f52])).
% 2.05/0.80  fof(f52,plain,(
% 2.05/0.80    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 2.05/0.80    inference(definition_unfolding,[],[f30,f50,f51])).
% 2.05/0.80  fof(f30,plain,(
% 2.05/0.80    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.05/0.80    inference(cnf_transformation,[],[f15])).
% 2.05/0.80  fof(f15,axiom,(
% 2.05/0.80    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.05/0.80  fof(f27,plain,(
% 2.05/0.80    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 2.05/0.80    inference(cnf_transformation,[],[f19])).
% 2.05/0.80  fof(f19,plain,(
% 2.05/0.80    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 2.05/0.80    inference(ennf_transformation,[],[f18])).
% 2.05/0.80  fof(f18,negated_conjecture,(
% 2.05/0.80    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 2.05/0.80    inference(negated_conjecture,[],[f17])).
% 2.05/0.80  fof(f17,conjecture,(
% 2.05/0.80    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 2.05/0.80  fof(f76,plain,(
% 2.05/0.80    ( ! [X12,X13] : (r1_tarski(X12,k3_tarski(k2_enumset1(X13,X13,X13,X12)))) )),
% 2.05/0.80    inference(superposition,[],[f54,f55])).
% 2.05/0.80  fof(f54,plain,(
% 2.05/0.80    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.05/0.80    inference(definition_unfolding,[],[f31,f50])).
% 2.05/0.80  fof(f31,plain,(
% 2.05/0.80    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.05/0.80    inference(cnf_transformation,[],[f6])).
% 2.05/0.80  fof(f6,axiom,(
% 2.05/0.80    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.05/0.80  fof(f1523,plain,(
% 2.05/0.80    ~spl2_28 | ~spl2_30),
% 2.05/0.80    inference(avatar_contradiction_clause,[],[f1514])).
% 2.05/0.80  fof(f1514,plain,(
% 2.05/0.80    $false | (~spl2_28 | ~spl2_30)),
% 2.05/0.80    inference(unit_resulting_resolution,[],[f1512,f552,f63])).
% 2.05/0.80  fof(f552,plain,(
% 2.05/0.80    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_28),
% 2.05/0.80    inference(avatar_component_clause,[],[f550])).
% 2.05/0.80  fof(f550,plain,(
% 2.05/0.80    spl2_28 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.05/0.80  fof(f1512,plain,(
% 2.05/0.80    ~r2_hidden(sK0,sK1) | ~spl2_30),
% 2.05/0.80    inference(resolution,[],[f1501,f37])).
% 2.05/0.80  fof(f1501,plain,(
% 2.05/0.80    r2_hidden(sK1,sK0) | ~spl2_30),
% 2.05/0.80    inference(resolution,[],[f1395,f32])).
% 2.05/0.80  fof(f1395,plain,(
% 2.05/0.80    ( ! [X9] : (~r1_tarski(k4_xboole_0(sK0,sK1),X9) | r2_hidden(sK1,X9)) ) | ~spl2_30),
% 2.05/0.80    inference(superposition,[],[f63,f627])).
% 2.05/0.80  fof(f627,plain,(
% 2.05/0.80    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_30),
% 2.05/0.80    inference(avatar_component_clause,[],[f625])).
% 2.05/0.80  fof(f625,plain,(
% 2.05/0.80    spl2_30 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1)),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 2.05/0.80  fof(f1511,plain,(
% 2.05/0.80    spl2_29 | ~spl2_30),
% 2.05/0.80    inference(avatar_contradiction_clause,[],[f1505])).
% 2.05/0.80  fof(f1505,plain,(
% 2.05/0.80    $false | (spl2_29 | ~spl2_30)),
% 2.05/0.80    inference(unit_resulting_resolution,[],[f67,f1466,f56])).
% 2.05/0.80  fof(f1466,plain,(
% 2.05/0.80    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK0,sK1)) | (spl2_29 | ~spl2_30)),
% 2.05/0.80    inference(forward_demodulation,[],[f556,f627])).
% 2.05/0.80  fof(f556,plain,(
% 2.05/0.80    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_29),
% 2.05/0.80    inference(avatar_component_clause,[],[f554])).
% 2.05/0.80  fof(f554,plain,(
% 2.05/0.80    spl2_29 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 2.05/0.80  fof(f1084,plain,(
% 2.05/0.80    spl2_5 | ~spl2_6 | ~spl2_3),
% 2.05/0.80    inference(avatar_split_clause,[],[f1080,f213,f231,f227])).
% 2.05/0.80  fof(f227,plain,(
% 2.05/0.80    spl2_5 <=> sK0 = sK1),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.05/0.80  fof(f231,plain,(
% 2.05/0.80    spl2_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.05/0.80  fof(f213,plain,(
% 2.05/0.80    spl2_3 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 2.05/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.05/0.80  fof(f1080,plain,(
% 2.05/0.80    k1_xboole_0 != k4_xboole_0(sK0,sK1) | sK0 = sK1 | ~spl2_3),
% 2.05/0.80    inference(superposition,[],[f38,f215])).
% 2.05/0.80  fof(f215,plain,(
% 2.05/0.80    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_3),
% 2.05/0.80    inference(avatar_component_clause,[],[f213])).
% 2.05/0.80  fof(f38,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 2.05/0.80    inference(cnf_transformation,[],[f22])).
% 2.05/0.80  fof(f22,plain,(
% 2.05/0.80    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 2.05/0.80    inference(ennf_transformation,[],[f2])).
% 2.05/0.80  fof(f2,axiom,(
% 2.05/0.80    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 2.05/0.80  fof(f659,plain,(
% 2.05/0.80    ~spl2_5),
% 2.05/0.80    inference(avatar_contradiction_clause,[],[f645])).
% 2.05/0.80  fof(f645,plain,(
% 2.05/0.80    $false | ~spl2_5),
% 2.05/0.80    inference(subsumption_resolution,[],[f28,f229])).
% 2.05/0.80  fof(f229,plain,(
% 2.05/0.80    sK0 = sK1 | ~spl2_5),
% 2.05/0.80    inference(avatar_component_clause,[],[f227])).
% 2.05/0.80  fof(f28,plain,(
% 2.05/0.80    sK0 != sK1),
% 2.05/0.80    inference(cnf_transformation,[],[f19])).
% 2.05/0.80  fof(f628,plain,(
% 2.05/0.80    spl2_6 | spl2_30),
% 2.05/0.80    inference(avatar_split_clause,[],[f621,f625,f231])).
% 2.05/0.80  fof(f621,plain,(
% 2.05/0.80    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.05/0.80    inference(resolution,[],[f509,f59])).
% 2.05/0.80  fof(f59,plain,(
% 2.05/0.80    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.05/0.80    inference(definition_unfolding,[],[f39,f51,f51])).
% 2.05/0.80  fof(f39,plain,(
% 2.05/0.80    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.05/0.80    inference(cnf_transformation,[],[f12])).
% 2.05/0.80  fof(f12,axiom,(
% 2.05/0.80    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.05/0.80  fof(f509,plain,(
% 2.05/0.80    r1_tarski(k4_xboole_0(sK0,sK1),k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.05/0.80    inference(resolution,[],[f186,f54])).
% 2.05/0.80  fof(f186,plain,(
% 2.05/0.80    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) | r1_tarski(k4_xboole_0(X0,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 2.05/0.80    inference(superposition,[],[f60,f53])).
% 2.05/0.80  fof(f60,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.05/0.80    inference(definition_unfolding,[],[f44,f50])).
% 2.05/0.80  fof(f44,plain,(
% 2.05/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.05/0.80    inference(cnf_transformation,[],[f24])).
% 2.05/0.80  fof(f24,plain,(
% 2.05/0.80    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.05/0.80    inference(ennf_transformation,[],[f4])).
% 2.05/0.80  fof(f4,axiom,(
% 2.05/0.80    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.05/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.05/0.80  fof(f557,plain,(
% 2.05/0.80    spl2_28 | ~spl2_29),
% 2.05/0.80    inference(avatar_split_clause,[],[f526,f554,f550])).
% 2.05/0.80  fof(f526,plain,(
% 2.05/0.80    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.05/0.80    inference(resolution,[],[f187,f76])).
% 2.05/0.80  fof(f187,plain,(
% 2.05/0.80    ( ! [X1] : (~r1_tarski(X1,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) | ~r1_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1)) | r1_tarski(X1,sK1)) )),
% 2.05/0.80    inference(superposition,[],[f61,f53])).
% 2.05/0.80  fof(f220,plain,(
% 2.05/0.80    spl2_3 | spl2_4),
% 2.05/0.80    inference(avatar_split_clause,[],[f210,f217,f213])).
% 2.05/0.80  fof(f210,plain,(
% 2.05/0.80    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0) | k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 2.05/0.80    inference(resolution,[],[f198,f59])).
% 2.05/0.80  fof(f198,plain,(
% 2.05/0.80    r1_tarski(k4_xboole_0(sK1,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.05/0.80    inference(resolution,[],[f185,f60])).
% 2.05/0.80  fof(f185,plain,(
% 2.05/0.80    r1_tarski(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.05/0.80    inference(superposition,[],[f54,f53])).
% 2.05/0.80  % SZS output end Proof for theBenchmark
% 2.05/0.80  % (7291)------------------------------
% 2.05/0.80  % (7291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.80  % (7291)Termination reason: Refutation
% 2.05/0.80  
% 2.05/0.80  % (7291)Memory used [KB]: 7419
% 2.05/0.80  % (7291)Time elapsed: 0.236 s
% 2.05/0.80  % (7291)------------------------------
% 2.05/0.80  % (7291)------------------------------
% 2.05/0.80  % (7117)Success in time 0.433 s
%------------------------------------------------------------------------------
