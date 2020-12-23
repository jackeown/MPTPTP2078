%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 209 expanded)
%              Number of leaves         :   33 (  99 expanded)
%              Depth                    :    7
%              Number of atoms          :  277 ( 461 expanded)
%              Number of equality atoms :   56 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2955,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f56,f60,f64,f74,f78,f85,f105,f113,f151,f155,f199,f213,f264,f268,f281,f489,f1383,f1574,f1586,f2232,f2948])).

fof(f2948,plain,
    ( ~ spl3_25
    | spl3_27
    | ~ spl3_111
    | ~ spl3_144 ),
    inference(avatar_contradiction_clause,[],[f2947])).

fof(f2947,plain,
    ( $false
    | ~ spl3_25
    | spl3_27
    | ~ spl3_111
    | ~ spl3_144 ),
    inference(subsumption_resolution,[],[f2946,f212])).

% (31174)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f212,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_27
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f2946,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_25
    | ~ spl3_111
    | ~ spl3_144 ),
    inference(forward_demodulation,[],[f2875,f198])).

fof(f198,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_25
  <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f2875,plain,
    ( k5_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_111
    | ~ spl3_144 ),
    inference(superposition,[],[f2231,f1585])).

fof(f1585,plain,
    ( sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_111 ),
    inference(avatar_component_clause,[],[f1583])).

fof(f1583,plain,
    ( spl3_111
  <=> sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).

fof(f2231,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ spl3_144 ),
    inference(avatar_component_clause,[],[f2230])).

fof(f2230,plain,
    ( spl3_144
  <=> ! [X1,X2] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_144])])).

fof(f2232,plain,
    ( spl3_144
    | ~ spl3_10
    | ~ spl3_37
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f699,f487,f266,f83,f2230])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f266,plain,
    ( spl3_37
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f487,plain,
    ( spl3_57
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f699,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ spl3_10
    | ~ spl3_37
    | ~ spl3_57 ),
    inference(backward_demodulation,[],[f359,f679])).

fof(f679,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl3_10
    | ~ spl3_57 ),
    inference(superposition,[],[f488,f84])).

fof(f84,plain,
    ( ! [X2] : k3_xboole_0(X2,X2) = X2
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f488,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f487])).

fof(f359,plain,
    ( ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ spl3_37 ),
    inference(superposition,[],[f267,f267])).

fof(f267,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f266])).

fof(f1586,plain,
    ( spl3_111
    | ~ spl3_9
    | ~ spl3_110 ),
    inference(avatar_split_clause,[],[f1580,f1571,f76,f1583])).

fof(f76,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1571,plain,
    ( spl3_110
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).

fof(f1580,plain,
    ( sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_110 ),
    inference(resolution,[],[f1573,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f1573,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_110 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f1574,plain,
    ( spl3_110
    | ~ spl3_15
    | ~ spl3_99 ),
    inference(avatar_split_clause,[],[f1543,f1381,f110,f1571])).

fof(f110,plain,
    ( spl3_15
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1381,plain,
    ( spl3_99
  <=> ! [X3,X5,X4] : r1_tarski(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),k3_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f1543,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_15
    | ~ spl3_99 ),
    inference(superposition,[],[f1382,f112])).

fof(f112,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1382,plain,
    ( ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),k3_xboole_0(X3,X4))
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f1383,plain,
    ( spl3_99
    | ~ spl3_6
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f689,f487,f62,f1381])).

fof(f62,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f689,plain,
    ( ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),k3_xboole_0(X3,X4))
    | ~ spl3_6
    | ~ spl3_57 ),
    inference(superposition,[],[f63,f488])).

fof(f63,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f489,plain,(
    spl3_57 ),
    inference(avatar_split_clause,[],[f38,f487])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f29,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f281,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f273,f262,f49,f44])).

fof(f44,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f262,plain,
    ( spl3_36
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f273,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_36 ),
    inference(resolution,[],[f263,f51])).

fof(f51,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f263,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f262])).

fof(f268,plain,(
    spl3_37 ),
    inference(avatar_split_clause,[],[f31,f266])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f264,plain,
    ( spl3_36
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f121,f103,f58,f262])).

fof(f58,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f103,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) )
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f104,f59])).

fof(f59,plain,
    ( ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f213,plain,
    ( ~ spl3_27
    | spl3_1
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f188,f153,f40,f210])).

fof(f40,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f153,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f188,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_21 ),
    inference(resolution,[],[f154,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f153])).

fof(f199,plain,
    ( spl3_25
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f167,f149,f83,f72,f197])).

fof(f72,plain,
    ( spl3_8
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f149,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f167,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f159,f84])).

fof(f159,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X3))
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(resolution,[],[f150,f73])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f155,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f37,f153])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f151,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f36,f149])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f79,f76,f49,f110])).

fof(f79,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f77,f51])).

fof(f105,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f30,f103])).

% (31162)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f85,plain,
    ( spl3_10
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f76,f72,f83])).

fof(f81,plain,
    ( ! [X2] : k3_xboole_0(X2,X2) = X2
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(resolution,[],[f77,f73])).

fof(f78,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f76])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f70,f62,f54,f72])).

fof(f54,plain,
    ( spl3_4
  <=> ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,
    ( ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f64,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f60,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f19,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f47,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f44,f40])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (31164)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (31157)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (31159)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (31158)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (31168)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (31167)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (31170)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (31164)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f2955,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f47,f52,f56,f60,f64,f74,f78,f85,f105,f113,f151,f155,f199,f213,f264,f268,f281,f489,f1383,f1574,f1586,f2232,f2948])).
% 0.20/0.49  fof(f2948,plain,(
% 0.20/0.49    ~spl3_25 | spl3_27 | ~spl3_111 | ~spl3_144),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f2947])).
% 0.20/0.49  fof(f2947,plain,(
% 0.20/0.49    $false | (~spl3_25 | spl3_27 | ~spl3_111 | ~spl3_144)),
% 0.20/0.49    inference(subsumption_resolution,[],[f2946,f212])).
% 0.20/0.49  % (31174)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f210])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    spl3_27 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f2946,plain,(
% 0.20/0.49    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_25 | ~spl3_111 | ~spl3_144)),
% 0.20/0.49    inference(forward_demodulation,[],[f2875,f198])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | ~spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f197])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    spl3_25 <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f2875,plain,(
% 0.20/0.49    k5_xboole_0(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_111 | ~spl3_144)),
% 0.20/0.49    inference(superposition,[],[f2231,f1585])).
% 0.20/0.49  fof(f1585,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_111),
% 0.20/0.49    inference(avatar_component_clause,[],[f1583])).
% 0.20/0.49  fof(f1583,plain,(
% 0.20/0.49    spl3_111 <=> sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).
% 0.20/0.49  fof(f2231,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) ) | ~spl3_144),
% 0.20/0.49    inference(avatar_component_clause,[],[f2230])).
% 0.20/0.49  fof(f2230,plain,(
% 0.20/0.49    spl3_144 <=> ! [X1,X2] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_144])])).
% 0.20/0.49  fof(f2232,plain,(
% 0.20/0.49    spl3_144 | ~spl3_10 | ~spl3_37 | ~spl3_57),
% 0.20/0.49    inference(avatar_split_clause,[],[f699,f487,f266,f83,f2230])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl3_10 <=> ! [X2] : k3_xboole_0(X2,X2) = X2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    spl3_37 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.49  fof(f487,plain,(
% 0.20/0.49    spl3_57 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.49  fof(f699,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) ) | (~spl3_10 | ~spl3_37 | ~spl3_57)),
% 0.20/0.49    inference(backward_demodulation,[],[f359,f679])).
% 0.20/0.49  fof(f679,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | (~spl3_10 | ~spl3_57)),
% 0.20/0.49    inference(superposition,[],[f488,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) ) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f488,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) ) | ~spl3_57),
% 0.20/0.49    inference(avatar_component_clause,[],[f487])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) ) | ~spl3_37),
% 0.20/0.49    inference(superposition,[],[f267,f267])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ) | ~spl3_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f266])).
% 0.20/0.49  fof(f1586,plain,(
% 0.20/0.49    spl3_111 | ~spl3_9 | ~spl3_110),
% 0.20/0.49    inference(avatar_split_clause,[],[f1580,f1571,f76,f1583])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f1571,plain,(
% 0.20/0.49    spl3_110 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).
% 0.20/0.49  fof(f1580,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_9 | ~spl3_110)),
% 0.20/0.49    inference(resolution,[],[f1573,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f1573,plain,(
% 0.20/0.49    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_110),
% 0.20/0.49    inference(avatar_component_clause,[],[f1571])).
% 0.20/0.49  fof(f1574,plain,(
% 0.20/0.49    spl3_110 | ~spl3_15 | ~spl3_99),
% 0.20/0.49    inference(avatar_split_clause,[],[f1543,f1381,f110,f1571])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl3_15 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f1381,plain,(
% 0.20/0.49    spl3_99 <=> ! [X3,X5,X4] : r1_tarski(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),k3_xboole_0(X3,X4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 0.20/0.49  fof(f1543,plain,(
% 0.20/0.49    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_15 | ~spl3_99)),
% 0.20/0.49    inference(superposition,[],[f1382,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f110])).
% 0.20/0.49  fof(f1382,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),k3_xboole_0(X3,X4))) ) | ~spl3_99),
% 0.20/0.49    inference(avatar_component_clause,[],[f1381])).
% 0.20/0.49  fof(f1383,plain,(
% 0.20/0.49    spl3_99 | ~spl3_6 | ~spl3_57),
% 0.20/0.49    inference(avatar_split_clause,[],[f689,f487,f62,f1381])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl3_6 <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f689,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),k3_xboole_0(X3,X4))) ) | (~spl3_6 | ~spl3_57)),
% 0.20/0.49    inference(superposition,[],[f63,f488])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f62])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    spl3_57),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f487])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f29,f25,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    spl3_2 | ~spl3_3 | ~spl3_36),
% 0.20/0.49    inference(avatar_split_clause,[],[f273,f262,f49,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    spl3_36 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X1) | ~r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_36)),
% 0.20/0.49    inference(resolution,[],[f263,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f263,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | r1_xboole_0(X0,X1)) ) | ~spl3_36),
% 0.20/0.49    inference(avatar_component_clause,[],[f262])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    spl3_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f266])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f24,f25,f25])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    spl3_36 | ~spl3_5 | ~spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f121,f103,f58,f262])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_5 <=> ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl3_14 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ) | (~spl3_5 | ~spl3_14)),
% 0.20/0.49    inference(resolution,[],[f104,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) ) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f58])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    ~spl3_27 | spl3_1 | ~spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f188,f153,f40,f210])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    spl3_21 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_21)),
% 0.20/0.49    inference(resolution,[],[f154,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f40])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f153])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl3_25 | ~spl3_8 | ~spl3_10 | ~spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f167,f149,f83,f72,f197])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_8 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    spl3_20 <=> ! [X1,X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | (~spl3_8 | ~spl3_10 | ~spl3_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f159,f84])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X3))) ) | (~spl3_8 | ~spl3_20)),
% 0.20/0.49    inference(resolution,[],[f150,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f149])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f153])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f27,f25])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f149])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f25])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl3_15 | ~spl3_3 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f79,f76,f49,f110])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl3_3 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f77,f51])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f103])).
% 0.20/0.49  % (31162)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_10 | ~spl3_8 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f81,f76,f72,f83])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) ) | (~spl3_8 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f77,f73])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f76])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_8 | ~spl3_4 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f70,f62,f54,f72])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_4 <=> ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_4 | ~spl3_6)),
% 0.20/0.49    inference(superposition,[],[f63,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) ) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f62])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f23,f25])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f58])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f25])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f54])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f25])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f49])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f25])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f44,f40])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (31164)------------------------------
% 0.20/0.49  % (31164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31164)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (31164)Memory used [KB]: 7931
% 0.20/0.49  % (31164)Time elapsed: 0.086 s
% 0.20/0.49  % (31164)------------------------------
% 0.20/0.49  % (31164)------------------------------
% 0.20/0.49  % (31165)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (31155)Success in time 0.135 s
%------------------------------------------------------------------------------
