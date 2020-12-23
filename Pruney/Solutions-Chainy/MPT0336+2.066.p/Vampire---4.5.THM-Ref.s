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
% DateTime   : Thu Dec  3 12:43:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 365 expanded)
%              Number of leaves         :   57 ( 173 expanded)
%              Depth                    :    8
%              Number of atoms          :  537 ( 952 expanded)
%              Number of equality atoms :   70 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2966,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f95,f99,f106,f111,f116,f124,f140,f156,f162,f225,f232,f291,f352,f356,f360,f531,f616,f715,f875,f920,f933,f1271,f1417,f1593,f1632,f1650,f1655,f2271,f2559,f2607,f2623,f2743,f2863,f2887,f2913,f2948])).

fof(f2948,plain,
    ( ~ spl6_58
    | spl6_120
    | ~ spl6_185 ),
    inference(avatar_contradiction_clause,[],[f2947])).

fof(f2947,plain,
    ( $false
    | ~ spl6_58
    | spl6_120
    | ~ spl6_185 ),
    inference(subsumption_resolution,[],[f2923,f1654])).

fof(f1654,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl6_120 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f1652,plain,
    ( spl6_120
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f2923,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_58
    | ~ spl6_185 ),
    inference(superposition,[],[f530,f2912])).

fof(f2912,plain,
    ( ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X7
    | ~ spl6_185 ),
    inference(avatar_component_clause,[],[f2911])).

fof(f2911,plain,
    ( spl6_185
  <=> ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_185])])).

fof(f530,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl6_58
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f2913,plain,
    ( spl6_185
    | ~ spl6_10
    | ~ spl6_184 ),
    inference(avatar_split_clause,[],[f2892,f2885,f122,f2911])).

fof(f122,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f2885,plain,
    ( spl6_184
  <=> ! [X8] : r1_xboole_0(X8,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_184])])).

fof(f2892,plain,
    ( ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X7
    | ~ spl6_10
    | ~ spl6_184 ),
    inference(resolution,[],[f2886,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f2886,plain,
    ( ! [X8] : r1_xboole_0(X8,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_184 ),
    inference(avatar_component_clause,[],[f2885])).

fof(f2887,plain,
    ( spl6_184
    | ~ spl6_5
    | ~ spl6_183 ),
    inference(avatar_split_clause,[],[f2869,f2861,f97,f2885])).

fof(f97,plain,
    ( spl6_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2861,plain,
    ( spl6_183
  <=> ! [X4] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).

fof(f2869,plain,
    ( ! [X8] : r1_xboole_0(X8,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_183 ),
    inference(resolution,[],[f2862,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f2862,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X4)
    | ~ spl6_183 ),
    inference(avatar_component_clause,[],[f2861])).

fof(f2863,plain,
    ( spl6_183
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_181 ),
    inference(avatar_split_clause,[],[f2859,f2741,f160,f153,f2861])).

fof(f153,plain,
    ( spl6_16
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f160,plain,
    ( spl6_17
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f2741,plain,
    ( spl6_181
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_181])])).

fof(f2859,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X4)
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_181 ),
    inference(forward_demodulation,[],[f2847,f161])).

fof(f161,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f2847,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),X4)
    | ~ spl6_16
    | ~ spl6_181 ),
    inference(superposition,[],[f2742,f155])).

fof(f155,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2742,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))),X1)
    | ~ spl6_181 ),
    inference(avatar_component_clause,[],[f2741])).

fof(f2743,plain,
    ( spl6_181
    | ~ spl6_111
    | ~ spl6_173
    | ~ spl6_177 ),
    inference(avatar_split_clause,[],[f2634,f2621,f2605,f1415,f2741])).

fof(f1415,plain,
    ( spl6_111
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f2605,plain,
    ( spl6_173
  <=> ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).

fof(f2621,plain,
    ( spl6_177
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_177])])).

fof(f2634,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))),X1)
    | ~ spl6_111
    | ~ spl6_173
    | ~ spl6_177 ),
    inference(forward_demodulation,[],[f2624,f2622])).

fof(f2622,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ spl6_177 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f2624,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK2))),X1)
    | ~ spl6_111
    | ~ spl6_173 ),
    inference(resolution,[],[f2606,f1416])).

fof(f1416,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) )
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f2606,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_173 ),
    inference(avatar_component_clause,[],[f2605])).

fof(f2623,plain,(
    spl6_177 ),
    inference(avatar_split_clause,[],[f76,f2621])).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f60,f46,f46,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f2607,plain,
    ( spl6_173
    | ~ spl6_93
    | ~ spl6_172 ),
    inference(avatar_split_clause,[],[f2564,f2557,f931,f2605])).

fof(f931,plain,
    ( spl6_93
  <=> ! [X4] : r1_xboole_0(k4_xboole_0(X4,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f2557,plain,
    ( spl6_172
  <=> ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).

fof(f2564,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_93
    | ~ spl6_172 ),
    inference(superposition,[],[f932,f2558])).

fof(f2558,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_172 ),
    inference(avatar_component_clause,[],[f2557])).

fof(f932,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(X4,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f931])).

fof(f2559,plain,
    ( spl6_172
    | ~ spl6_7
    | ~ spl6_155 ),
    inference(avatar_split_clause,[],[f2278,f2269,f109,f2557])).

fof(f109,plain,
    ( spl6_7
  <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f2269,plain,
    ( spl6_155
  <=> ! [X32] :
        ( k4_xboole_0(X32,k2_enumset1(sK3,sK3,sK3,sK3)) = X32
        | ~ r1_xboole_0(sK2,X32) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).

fof(f2278,plain,
    ( ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_7
    | ~ spl6_155 ),
    inference(resolution,[],[f2270,f110])).

fof(f110,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f2270,plain,
    ( ! [X32] :
        ( ~ r1_xboole_0(sK2,X32)
        | k4_xboole_0(X32,k2_enumset1(sK3,sK3,sK3,sK3)) = X32 )
    | ~ spl6_155 ),
    inference(avatar_component_clause,[],[f2269])).

fof(f2271,plain,
    ( spl6_155
    | ~ spl6_26
    | ~ spl6_119 ),
    inference(avatar_split_clause,[],[f2216,f1648,f230,f2269])).

fof(f230,plain,
    ( spl6_26
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1648,plain,
    ( spl6_119
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f2216,plain,
    ( ! [X32] :
        ( k4_xboole_0(X32,k2_enumset1(sK3,sK3,sK3,sK3)) = X32
        | ~ r1_xboole_0(sK2,X32) )
    | ~ spl6_26
    | ~ spl6_119 ),
    inference(resolution,[],[f1649,f231])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f1649,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 )
    | ~ spl6_119 ),
    inference(avatar_component_clause,[],[f1648])).

fof(f1655,plain,
    ( ~ spl6_120
    | ~ spl6_82
    | spl6_116 ),
    inference(avatar_split_clause,[],[f1633,f1629,f713,f1652])).

fof(f713,plain,
    ( spl6_82
  <=> ! [X3,X2] :
        ( k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
        | r1_xboole_0(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f1629,plain,
    ( spl6_116
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f1633,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_82
    | spl6_116 ),
    inference(resolution,[],[f1631,f714])).

fof(f714,plain,
    ( ! [X2,X3] :
        ( r1_xboole_0(X3,X2)
        | k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) )
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f713])).

fof(f1631,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_116 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1650,plain,(
    spl6_119 ),
    inference(avatar_split_clause,[],[f74,f1648])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f1632,plain,
    ( ~ spl6_116
    | spl6_3
    | ~ spl6_6
    | ~ spl6_114 ),
    inference(avatar_split_clause,[],[f1627,f1591,f103,f88,f1629])).

fof(f88,plain,
    ( spl6_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f103,plain,
    ( spl6_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1591,plain,
    ( spl6_114
  <=> ! [X29,X28,X30] :
        ( ~ r1_xboole_0(X28,X29)
        | ~ r1_xboole_0(X28,X30)
        | r1_xboole_0(k2_xboole_0(X29,X30),X28) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f1627,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_3
    | ~ spl6_6
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f1610,f105])).

fof(f105,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1610,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl6_3
    | ~ spl6_114 ),
    inference(resolution,[],[f1592,f90])).

fof(f90,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1592,plain,
    ( ! [X30,X28,X29] :
        ( r1_xboole_0(k2_xboole_0(X29,X30),X28)
        | ~ r1_xboole_0(X28,X30)
        | ~ r1_xboole_0(X28,X29) )
    | ~ spl6_114 ),
    inference(avatar_component_clause,[],[f1591])).

fof(f1593,plain,
    ( spl6_114
    | ~ spl6_5
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f953,f614,f97,f1591])).

fof(f614,plain,
    ( spl6_65
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f953,plain,
    ( ! [X30,X28,X29] :
        ( ~ r1_xboole_0(X28,X29)
        | ~ r1_xboole_0(X28,X30)
        | r1_xboole_0(k2_xboole_0(X29,X30),X28) )
    | ~ spl6_5
    | ~ spl6_65 ),
    inference(resolution,[],[f615,f98])).

fof(f615,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X2) )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f614])).

fof(f1417,plain,
    ( spl6_111
    | ~ spl6_8
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f1272,f1269,f114,f1415])).

fof(f114,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1269,plain,
    ( spl6_100
  <=> ! [X11,X10,X12] :
        ( ~ r2_hidden(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10)))
        | ~ r1_xboole_0(X10,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1272,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) )
    | ~ spl6_8
    | ~ spl6_100 ),
    inference(resolution,[],[f1270,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1270,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10)))
        | ~ r1_xboole_0(X10,X11) )
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1269])).

fof(f1271,plain,
    ( spl6_100
    | ~ spl6_41
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f1016,f873,f350,f1269])).

fof(f350,plain,
    ( spl6_41
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f873,plain,
    ( spl6_87
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f1016,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10)))
        | ~ r1_xboole_0(X10,X11) )
    | ~ spl6_41
    | ~ spl6_87 ),
    inference(superposition,[],[f351,f874])).

fof(f874,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f873])).

fof(f351,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f350])).

fof(f933,plain,
    ( spl6_93
    | ~ spl6_5
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f924,f918,f97,f931])).

fof(f918,plain,
    ( spl6_92
  <=> ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f924,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(X4,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_92 ),
    inference(resolution,[],[f919,f98])).

fof(f919,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f918])).

fof(f920,plain,
    ( spl6_92
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f348,f288,f138,f918])).

fof(f138,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f288,plain,
    ( spl6_34
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f348,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(resolution,[],[f290,f139])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_xboole_0(X0,k4_xboole_0(X2,X1)) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f290,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f288])).

fof(f875,plain,(
    spl6_87 ),
    inference(avatar_split_clause,[],[f69,f873])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f46,f46])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f715,plain,
    ( spl6_82
    | ~ spl6_5
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f379,f354,f97,f713])).

fof(f354,plain,
    ( spl6_42
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f379,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
        | r1_xboole_0(X3,X2) )
    | ~ spl6_5
    | ~ spl6_42 ),
    inference(resolution,[],[f355,f98])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f354])).

fof(f616,plain,(
    spl6_65 ),
    inference(avatar_split_clause,[],[f61,f614])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f531,plain,
    ( spl6_58
    | ~ spl6_7
    | ~ spl6_17
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f478,f358,f160,f109,f529])).

fof(f358,plain,
    ( spl6_43
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f478,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl6_7
    | ~ spl6_17
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f456,f161])).

fof(f456,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl6_7
    | ~ spl6_43 ),
    inference(resolution,[],[f359,f110])).

fof(f359,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f358])).

fof(f360,plain,(
    spl6_43 ),
    inference(avatar_split_clause,[],[f73,f358])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f46])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f356,plain,(
    spl6_42 ),
    inference(avatar_split_clause,[],[f72,f354])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f56,f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f352,plain,(
    spl6_41 ),
    inference(avatar_split_clause,[],[f70,f350])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f291,plain,(
    spl6_34 ),
    inference(avatar_split_clause,[],[f68,f288])).

fof(f68,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f37,f46,f66])).

fof(f37,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f232,plain,
    ( spl6_26
    | ~ spl6_1
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f226,f223,f78,f230])).

fof(f78,plain,
    ( spl6_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f223,plain,
    ( spl6_25
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl6_1
    | ~ spl6_25 ),
    inference(resolution,[],[f224,f80])).

fof(f80,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f51,f223])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f162,plain,
    ( spl6_17
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f141,f122,f109,f160])).

fof(f141,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(resolution,[],[f123,f110])).

fof(f156,plain,
    ( spl6_16
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f143,f122,f103,f153])).

fof(f143,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(resolution,[],[f123,f105])).

fof(f140,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f64,f138])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f124,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f116,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f49,f114])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,
    ( spl6_7
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f101,f97,f93,f109])).

fof(f93,plain,
    ( spl6_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f101,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f98,f94])).

fof(f94,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,
    ( spl6_6
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f100,f97,f83,f103])).

fof(f83,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f100,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(resolution,[],[f98,f85])).

fof(f85,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f99,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f95,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f91,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f40,f88])).

fof(f40,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (2939)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (2950)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (2943)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (2954)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (2949)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (2947)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (2940)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (2951)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (2946)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (2944)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (2942)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (2941)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (2953)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (2955)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (2945)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (2948)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (2952)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (2956)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.57  % (2946)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f2966,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f81,f86,f91,f95,f99,f106,f111,f116,f124,f140,f156,f162,f225,f232,f291,f352,f356,f360,f531,f616,f715,f875,f920,f933,f1271,f1417,f1593,f1632,f1650,f1655,f2271,f2559,f2607,f2623,f2743,f2863,f2887,f2913,f2948])).
% 0.20/0.57  fof(f2948,plain,(
% 0.20/0.57    ~spl6_58 | spl6_120 | ~spl6_185),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f2947])).
% 0.20/0.57  fof(f2947,plain,(
% 0.20/0.57    $false | (~spl6_58 | spl6_120 | ~spl6_185)),
% 0.20/0.57    inference(subsumption_resolution,[],[f2923,f1654])).
% 0.20/0.57  fof(f1654,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl6_120),
% 0.20/0.57    inference(avatar_component_clause,[],[f1652])).
% 0.20/0.57  fof(f1652,plain,(
% 0.20/0.57    spl6_120 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).
% 0.20/0.57  fof(f2923,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl6_58 | ~spl6_185)),
% 0.20/0.57    inference(superposition,[],[f530,f2912])).
% 0.20/0.57  fof(f2912,plain,(
% 0.20/0.57    ( ! [X7] : (k4_xboole_0(X7,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X7) ) | ~spl6_185),
% 0.20/0.57    inference(avatar_component_clause,[],[f2911])).
% 0.20/0.57  fof(f2911,plain,(
% 0.20/0.57    spl6_185 <=> ! [X7] : k4_xboole_0(X7,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X7),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_185])])).
% 0.20/0.57  fof(f530,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl6_58),
% 0.20/0.57    inference(avatar_component_clause,[],[f529])).
% 0.20/0.57  fof(f529,plain,(
% 0.20/0.57    spl6_58 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.20/0.57  fof(f2913,plain,(
% 0.20/0.57    spl6_185 | ~spl6_10 | ~spl6_184),
% 0.20/0.57    inference(avatar_split_clause,[],[f2892,f2885,f122,f2911])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    spl6_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.57  fof(f2885,plain,(
% 0.20/0.57    spl6_184 <=> ! [X8] : r1_xboole_0(X8,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_184])])).
% 0.20/0.57  fof(f2892,plain,(
% 0.20/0.57    ( ! [X7] : (k4_xboole_0(X7,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X7) ) | (~spl6_10 | ~spl6_184)),
% 0.20/0.57    inference(resolution,[],[f2886,f123])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl6_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f122])).
% 0.20/0.57  fof(f2886,plain,(
% 0.20/0.57    ( ! [X8] : (r1_xboole_0(X8,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_184),
% 0.20/0.57    inference(avatar_component_clause,[],[f2885])).
% 0.20/0.57  fof(f2887,plain,(
% 0.20/0.57    spl6_184 | ~spl6_5 | ~spl6_183),
% 0.20/0.57    inference(avatar_split_clause,[],[f2869,f2861,f97,f2885])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    spl6_5 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.57  fof(f2861,plain,(
% 0.20/0.57    spl6_183 <=> ! [X4] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).
% 0.20/0.57  fof(f2869,plain,(
% 0.20/0.57    ( ! [X8] : (r1_xboole_0(X8,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl6_5 | ~spl6_183)),
% 0.20/0.57    inference(resolution,[],[f2862,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl6_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f97])).
% 0.20/0.57  fof(f2862,plain,(
% 0.20/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X4)) ) | ~spl6_183),
% 0.20/0.57    inference(avatar_component_clause,[],[f2861])).
% 0.20/0.57  fof(f2863,plain,(
% 0.20/0.57    spl6_183 | ~spl6_16 | ~spl6_17 | ~spl6_181),
% 0.20/0.57    inference(avatar_split_clause,[],[f2859,f2741,f160,f153,f2861])).
% 0.20/0.57  fof(f153,plain,(
% 0.20/0.57    spl6_16 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.57  fof(f160,plain,(
% 0.20/0.57    spl6_17 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.57  fof(f2741,plain,(
% 0.20/0.57    spl6_181 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))),X1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_181])])).
% 0.20/0.57  fof(f2859,plain,(
% 0.20/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X4)) ) | (~spl6_16 | ~spl6_17 | ~spl6_181)),
% 0.20/0.57    inference(forward_demodulation,[],[f2847,f161])).
% 0.20/0.57  fof(f161,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) ) | ~spl6_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f160])).
% 0.20/0.57  fof(f2847,plain,(
% 0.20/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),X4)) ) | (~spl6_16 | ~spl6_181)),
% 0.20/0.57    inference(superposition,[],[f2742,f155])).
% 0.20/0.57  fof(f155,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,sK2) | ~spl6_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f153])).
% 0.20/0.57  fof(f2742,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))),X1)) ) | ~spl6_181),
% 0.20/0.57    inference(avatar_component_clause,[],[f2741])).
% 0.20/0.57  fof(f2743,plain,(
% 0.20/0.57    spl6_181 | ~spl6_111 | ~spl6_173 | ~spl6_177),
% 0.20/0.57    inference(avatar_split_clause,[],[f2634,f2621,f2605,f1415,f2741])).
% 0.20/0.57  fof(f1415,plain,(
% 0.20/0.57    spl6_111 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 0.20/0.57  fof(f2605,plain,(
% 0.20/0.57    spl6_173 <=> ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).
% 0.20/0.57  fof(f2621,plain,(
% 0.20/0.57    spl6_177 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_177])])).
% 0.20/0.57  fof(f2634,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))),X1)) ) | (~spl6_111 | ~spl6_173 | ~spl6_177)),
% 0.20/0.57    inference(forward_demodulation,[],[f2624,f2622])).
% 0.20/0.57  fof(f2622,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ) | ~spl6_177),
% 0.20/0.57    inference(avatar_component_clause,[],[f2621])).
% 0.20/0.57  fof(f2624,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK2))),X1)) ) | (~spl6_111 | ~spl6_173)),
% 0.20/0.57    inference(resolution,[],[f2606,f1416])).
% 0.20/0.57  fof(f1416,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | ~spl6_111),
% 0.20/0.57    inference(avatar_component_clause,[],[f1415])).
% 0.20/0.57  fof(f2606,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_173),
% 0.20/0.57    inference(avatar_component_clause,[],[f2605])).
% 0.20/0.57  fof(f2623,plain,(
% 0.20/0.57    spl6_177),
% 0.20/0.57    inference(avatar_split_clause,[],[f76,f2621])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f60,f46,f46,f46,f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.57  fof(f2607,plain,(
% 0.20/0.57    spl6_173 | ~spl6_93 | ~spl6_172),
% 0.20/0.57    inference(avatar_split_clause,[],[f2564,f2557,f931,f2605])).
% 0.20/0.57  fof(f931,plain,(
% 0.20/0.57    spl6_93 <=> ! [X4] : r1_xboole_0(k4_xboole_0(X4,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 0.20/0.57  fof(f2557,plain,(
% 0.20/0.57    spl6_172 <=> ! [X4] : k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).
% 0.20/0.57  fof(f2564,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl6_93 | ~spl6_172)),
% 0.20/0.57    inference(superposition,[],[f932,f2558])).
% 0.20/0.57  fof(f2558,plain,(
% 0.20/0.57    ( ! [X4] : (k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ) | ~spl6_172),
% 0.20/0.57    inference(avatar_component_clause,[],[f2557])).
% 0.20/0.57  fof(f932,plain,(
% 0.20/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(X4,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_93),
% 0.20/0.57    inference(avatar_component_clause,[],[f931])).
% 0.20/0.57  fof(f2559,plain,(
% 0.20/0.57    spl6_172 | ~spl6_7 | ~spl6_155),
% 0.20/0.57    inference(avatar_split_clause,[],[f2278,f2269,f109,f2557])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    spl6_7 <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.57  fof(f2269,plain,(
% 0.20/0.57    spl6_155 <=> ! [X32] : (k4_xboole_0(X32,k2_enumset1(sK3,sK3,sK3,sK3)) = X32 | ~r1_xboole_0(sK2,X32))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).
% 0.20/0.57  fof(f2278,plain,(
% 0.20/0.57    ( ! [X4] : (k4_xboole_0(X4,sK2) = k4_xboole_0(k4_xboole_0(X4,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ) | (~spl6_7 | ~spl6_155)),
% 0.20/0.57    inference(resolution,[],[f2270,f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl6_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f109])).
% 0.20/0.57  fof(f2270,plain,(
% 0.20/0.57    ( ! [X32] : (~r1_xboole_0(sK2,X32) | k4_xboole_0(X32,k2_enumset1(sK3,sK3,sK3,sK3)) = X32) ) | ~spl6_155),
% 0.20/0.57    inference(avatar_component_clause,[],[f2269])).
% 0.20/0.57  fof(f2271,plain,(
% 0.20/0.57    spl6_155 | ~spl6_26 | ~spl6_119),
% 0.20/0.57    inference(avatar_split_clause,[],[f2216,f1648,f230,f2269])).
% 0.20/0.57  fof(f230,plain,(
% 0.20/0.57    spl6_26 <=> ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.57  fof(f1648,plain,(
% 0.20/0.57    spl6_119 <=> ! [X1,X0] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).
% 0.20/0.57  fof(f2216,plain,(
% 0.20/0.57    ( ! [X32] : (k4_xboole_0(X32,k2_enumset1(sK3,sK3,sK3,sK3)) = X32 | ~r1_xboole_0(sK2,X32)) ) | (~spl6_26 | ~spl6_119)),
% 0.20/0.57    inference(resolution,[],[f1649,f231])).
% 0.20/0.57  fof(f231,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl6_26),
% 0.20/0.57    inference(avatar_component_clause,[],[f230])).
% 0.20/0.57  fof(f1649,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) ) | ~spl6_119),
% 0.20/0.57    inference(avatar_component_clause,[],[f1648])).
% 0.20/0.57  fof(f1655,plain,(
% 0.20/0.57    ~spl6_120 | ~spl6_82 | spl6_116),
% 0.20/0.57    inference(avatar_split_clause,[],[f1633,f1629,f713,f1652])).
% 0.20/0.57  fof(f713,plain,(
% 0.20/0.57    spl6_82 <=> ! [X3,X2] : (k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) | r1_xboole_0(X3,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 0.20/0.57  fof(f1629,plain,(
% 0.20/0.57    spl6_116 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).
% 0.20/0.57  fof(f1633,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl6_82 | spl6_116)),
% 0.20/0.57    inference(resolution,[],[f1631,f714])).
% 0.20/0.57  fof(f714,plain,(
% 0.20/0.57    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3))) ) | ~spl6_82),
% 0.20/0.57    inference(avatar_component_clause,[],[f713])).
% 0.20/0.57  fof(f1631,plain,(
% 0.20/0.57    ~r1_xboole_0(sK1,sK0) | spl6_116),
% 0.20/0.57    inference(avatar_component_clause,[],[f1629])).
% 0.20/0.57  fof(f1650,plain,(
% 0.20/0.57    spl6_119),
% 0.20/0.57    inference(avatar_split_clause,[],[f74,f1648])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f58,f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f41,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f44,f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.57  fof(f1632,plain,(
% 0.20/0.57    ~spl6_116 | spl6_3 | ~spl6_6 | ~spl6_114),
% 0.20/0.57    inference(avatar_split_clause,[],[f1627,f1591,f103,f88,f1629])).
% 0.20/0.57  fof(f88,plain,(
% 0.20/0.57    spl6_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    spl6_6 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.57  fof(f1591,plain,(
% 0.20/0.57    spl6_114 <=> ! [X29,X28,X30] : (~r1_xboole_0(X28,X29) | ~r1_xboole_0(X28,X30) | r1_xboole_0(k2_xboole_0(X29,X30),X28))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).
% 0.20/0.57  fof(f1627,plain,(
% 0.20/0.57    ~r1_xboole_0(sK1,sK0) | (spl6_3 | ~spl6_6 | ~spl6_114)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1610,f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK2) | ~spl6_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f103])).
% 0.20/0.57  fof(f1610,plain,(
% 0.20/0.57    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | (spl6_3 | ~spl6_114)),
% 0.20/0.57    inference(resolution,[],[f1592,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl6_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f88])).
% 0.20/0.57  fof(f1592,plain,(
% 0.20/0.57    ( ! [X30,X28,X29] : (r1_xboole_0(k2_xboole_0(X29,X30),X28) | ~r1_xboole_0(X28,X30) | ~r1_xboole_0(X28,X29)) ) | ~spl6_114),
% 0.20/0.57    inference(avatar_component_clause,[],[f1591])).
% 0.20/0.57  fof(f1593,plain,(
% 0.20/0.57    spl6_114 | ~spl6_5 | ~spl6_65),
% 0.20/0.57    inference(avatar_split_clause,[],[f953,f614,f97,f1591])).
% 0.20/0.57  fof(f614,plain,(
% 0.20/0.57    spl6_65 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.20/0.57  fof(f953,plain,(
% 0.20/0.57    ( ! [X30,X28,X29] : (~r1_xboole_0(X28,X29) | ~r1_xboole_0(X28,X30) | r1_xboole_0(k2_xboole_0(X29,X30),X28)) ) | (~spl6_5 | ~spl6_65)),
% 0.20/0.57    inference(resolution,[],[f615,f98])).
% 0.20/0.57  fof(f615,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) ) | ~spl6_65),
% 0.20/0.57    inference(avatar_component_clause,[],[f614])).
% 0.20/0.57  fof(f1417,plain,(
% 0.20/0.57    spl6_111 | ~spl6_8 | ~spl6_100),
% 0.20/0.57    inference(avatar_split_clause,[],[f1272,f1269,f114,f1415])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    spl6_8 <=> ! [X1,X0] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.57  fof(f1269,plain,(
% 0.20/0.57    spl6_100 <=> ! [X11,X10,X12] : (~r2_hidden(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10))) | ~r1_xboole_0(X10,X11))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 0.20/0.57  fof(f1272,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | (~spl6_8 | ~spl6_100)),
% 0.20/0.57    inference(resolution,[],[f1270,f115])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl6_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f114])).
% 0.20/0.57  fof(f1270,plain,(
% 0.20/0.57    ( ! [X12,X10,X11] : (~r2_hidden(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10))) | ~r1_xboole_0(X10,X11)) ) | ~spl6_100),
% 0.20/0.57    inference(avatar_component_clause,[],[f1269])).
% 0.20/0.57  fof(f1271,plain,(
% 0.20/0.57    spl6_100 | ~spl6_41 | ~spl6_87),
% 0.20/0.57    inference(avatar_split_clause,[],[f1016,f873,f350,f1269])).
% 0.20/0.57  fof(f350,plain,(
% 0.20/0.57    spl6_41 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.57  fof(f873,plain,(
% 0.20/0.57    spl6_87 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 0.20/0.57  fof(f1016,plain,(
% 0.20/0.57    ( ! [X12,X10,X11] : (~r2_hidden(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10))) | ~r1_xboole_0(X10,X11)) ) | (~spl6_41 | ~spl6_87)),
% 0.20/0.57    inference(superposition,[],[f351,f874])).
% 0.20/0.57  fof(f874,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl6_87),
% 0.20/0.57    inference(avatar_component_clause,[],[f873])).
% 0.20/0.57  fof(f351,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) ) | ~spl6_41),
% 0.20/0.57    inference(avatar_component_clause,[],[f350])).
% 0.20/0.57  fof(f933,plain,(
% 0.20/0.57    spl6_93 | ~spl6_5 | ~spl6_92),
% 0.20/0.57    inference(avatar_split_clause,[],[f924,f918,f97,f931])).
% 0.20/0.57  fof(f918,plain,(
% 0.20/0.57    spl6_92 <=> ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 0.20/0.57  fof(f924,plain,(
% 0.20/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(X4,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl6_5 | ~spl6_92)),
% 0.20/0.57    inference(resolution,[],[f919,f98])).
% 0.20/0.57  fof(f919,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)))) ) | ~spl6_92),
% 0.20/0.57    inference(avatar_component_clause,[],[f918])).
% 0.20/0.57  fof(f920,plain,(
% 0.20/0.57    spl6_92 | ~spl6_14 | ~spl6_34),
% 0.20/0.57    inference(avatar_split_clause,[],[f348,f288,f138,f918])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    spl6_14 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.57  fof(f288,plain,(
% 0.20/0.57    spl6_34 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.57  fof(f348,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k2_enumset1(sK3,sK3,sK3,sK3)))) ) | (~spl6_14 | ~spl6_34)),
% 0.20/0.57    inference(resolution,[],[f290,f139])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) ) | ~spl6_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f138])).
% 0.20/0.57  fof(f290,plain,(
% 0.20/0.57    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_34),
% 0.20/0.57    inference(avatar_component_clause,[],[f288])).
% 0.20/0.57  fof(f875,plain,(
% 0.20/0.57    spl6_87),
% 0.20/0.57    inference(avatar_split_clause,[],[f69,f873])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f43,f46,f46])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.57  fof(f715,plain,(
% 0.20/0.57    spl6_82 | ~spl6_5 | ~spl6_42),
% 0.20/0.57    inference(avatar_split_clause,[],[f379,f354,f97,f713])).
% 0.20/0.57  fof(f354,plain,(
% 0.20/0.57    spl6_42 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.20/0.57  fof(f379,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) | r1_xboole_0(X3,X2)) ) | (~spl6_5 | ~spl6_42)),
% 0.20/0.57    inference(resolution,[],[f355,f98])).
% 0.20/0.57  fof(f355,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl6_42),
% 0.20/0.57    inference(avatar_component_clause,[],[f354])).
% 0.20/0.57  fof(f616,plain,(
% 0.20/0.57    spl6_65),
% 0.20/0.57    inference(avatar_split_clause,[],[f61,f614])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.57  fof(f531,plain,(
% 0.20/0.57    spl6_58 | ~spl6_7 | ~spl6_17 | ~spl6_43),
% 0.20/0.57    inference(avatar_split_clause,[],[f478,f358,f160,f109,f529])).
% 0.20/0.57  fof(f358,plain,(
% 0.20/0.57    spl6_43 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.57  fof(f478,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl6_7 | ~spl6_17 | ~spl6_43)),
% 0.20/0.57    inference(forward_demodulation,[],[f456,f161])).
% 0.20/0.57  fof(f456,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | (~spl6_7 | ~spl6_43)),
% 0.20/0.57    inference(resolution,[],[f359,f110])).
% 0.20/0.57  fof(f359,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl6_43),
% 0.20/0.57    inference(avatar_component_clause,[],[f358])).
% 0.20/0.57  fof(f360,plain,(
% 0.20/0.57    spl6_43),
% 0.20/0.57    inference(avatar_split_clause,[],[f73,f358])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f55,f46])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.57  fof(f356,plain,(
% 0.20/0.57    spl6_42),
% 0.20/0.57    inference(avatar_split_clause,[],[f72,f354])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f56,f46])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f352,plain,(
% 0.20/0.57    spl6_41),
% 0.20/0.57    inference(avatar_split_clause,[],[f70,f350])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f48,f46])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.57  fof(f291,plain,(
% 0.20/0.57    spl6_34),
% 0.20/0.57    inference(avatar_split_clause,[],[f68,f288])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.57    inference(definition_unfolding,[],[f37,f46,f66])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.20/0.57    inference(flattening,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.57    inference(negated_conjecture,[],[f17])).
% 0.20/0.57  fof(f17,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.20/0.57  fof(f232,plain,(
% 0.20/0.57    spl6_26 | ~spl6_1 | ~spl6_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f226,f223,f78,f230])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    spl6_1 <=> r2_hidden(sK3,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.57  fof(f223,plain,(
% 0.20/0.57    spl6_25 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.57  fof(f226,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | (~spl6_1 | ~spl6_25)),
% 0.20/0.57    inference(resolution,[],[f224,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    r2_hidden(sK3,sK2) | ~spl6_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f78])).
% 0.20/0.57  fof(f224,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) ) | ~spl6_25),
% 0.20/0.57    inference(avatar_component_clause,[],[f223])).
% 0.20/0.57  fof(f225,plain,(
% 0.20/0.57    spl6_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f51,f223])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.57  fof(f162,plain,(
% 0.20/0.57    spl6_17 | ~spl6_7 | ~spl6_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f141,f122,f109,f160])).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) ) | (~spl6_7 | ~spl6_10)),
% 0.20/0.57    inference(resolution,[],[f123,f110])).
% 0.20/0.57  fof(f156,plain,(
% 0.20/0.57    spl6_16 | ~spl6_6 | ~spl6_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f143,f122,f103,f153])).
% 0.20/0.57  fof(f143,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,sK2) | (~spl6_6 | ~spl6_10)),
% 0.20/0.57    inference(resolution,[],[f123,f105])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    spl6_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f64,f138])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    spl6_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f53,f122])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    spl6_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f49,f114])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    spl6_7 | ~spl6_4 | ~spl6_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f101,f97,f93,f109])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    spl6_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | (~spl6_4 | ~spl6_5)),
% 0.20/0.57    inference(resolution,[],[f98,f94])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl6_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f93])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    spl6_6 | ~spl6_2 | ~spl6_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f100,f97,f83,f103])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK2) | (~spl6_2 | ~spl6_5)),
% 0.20/0.57    inference(resolution,[],[f98,f85])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f83])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl6_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f52,f97])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    spl6_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f42,f93])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ~spl6_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f40,f88])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    spl6_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f39,f83])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    r1_xboole_0(sK2,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    spl6_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f38,f78])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    r2_hidden(sK3,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (2946)------------------------------
% 0.20/0.57  % (2946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (2946)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (2946)Memory used [KB]: 8187
% 0.20/0.57  % (2946)Time elapsed: 0.146 s
% 0.20/0.57  % (2946)------------------------------
% 0.20/0.57  % (2946)------------------------------
% 0.20/0.57  % (2938)Success in time 0.211 s
%------------------------------------------------------------------------------
