%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 166 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 322 expanded)
%              Number of equality atoms :   80 ( 177 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32326)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (32317)Termination reason: Refutation not found, incomplete strategy

% (32317)Memory used [KB]: 10618
% (32317)Time elapsed: 0.100 s
% (32317)------------------------------
% (32317)------------------------------
% (32327)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (32324)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (32323)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (32330)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (32321)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (32331)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f436,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f113,f145,f179,f431,f435])).

fof(f435,plain,
    ( ~ spl5_4
    | spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f434,f428,f103,f142])).

fof(f142,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f103,plain,
    ( spl5_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f428,plain,
    ( spl5_12
  <=> sK1 = sK3(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f434,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_2
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f432])).

fof(f432,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 != sK0
    | sK1 != sK1
    | spl5_2
    | ~ spl5_12 ),
    inference(superposition,[],[f108,f430])).

fof(f430,plain,
    ( sK1 = sK3(sK1,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f428])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK1,X1),X1)
        | sK0 != X1
        | sK1 != sK3(sK1,X1) )
    | spl5_2 ),
    inference(superposition,[],[f105,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f105,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f431,plain,
    ( spl5_12
    | spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f426,f176,f110,f103,f428])).

fof(f110,plain,
    ( spl5_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f176,plain,
    ( spl5_9
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f426,plain,
    ( sK1 = sK3(sK1,sK0)
    | spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(trivial_inequality_removal,[],[f425])).

fof(f425,plain,
    ( sK1 = sK3(sK1,sK0)
    | sK0 != sK0
    | spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f424])).

fof(f424,plain,
    ( sK1 = sK3(sK1,sK0)
    | sK0 != sK0
    | sK1 = sK3(sK1,sK0)
    | spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f410,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,X0),X0)
        | sK0 != X0
        | sK1 = sK3(sK1,X0) )
    | spl5_2 ),
    inference(superposition,[],[f105,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f410,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 = X0 )
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f400,f190])).

fof(f190,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f184,f133])).

fof(f133,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,k1_xboole_0) )
    | ~ spl5_3 ),
    inference(superposition,[],[f96,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_9 ),
    inference(superposition,[],[f62,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f176])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f400,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | sK1 = X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f131,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f131,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl5_3 ),
    inference(superposition,[],[f94,f112])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f37])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f179,plain,
    ( spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f169,f110,f176])).

fof(f169,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0)
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f112,f139])).

fof(f139,plain,
    ( sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f124,f71])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f124,plain,
    ( k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl5_3 ),
    inference(superposition,[],[f68,f112])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f35,f37,f37])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f145,plain,
    ( spl5_4
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f116,f110,f98,f142])).

fof(f98,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f116,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0)
    | ~ spl5_3 ),
    inference(superposition,[],[f112,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f52,f37,f66])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f113,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f70,f110])).

fof(f70,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f26,f37,f66])).

fof(f26,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f106,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f69,f103])).

fof(f69,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f28,f66])).

fof(f28,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f27,f98])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:38:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (32314)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (32309)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (32317)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (32315)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (32308)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (32328)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (32316)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (32310)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (32312)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (32329)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (32334)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (32311)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (32313)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (32325)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (32317)Refutation not found, incomplete strategy% (32317)------------------------------
% 0.21/0.51  % (32317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32319)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (32322)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (32336)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (32307)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (32333)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (32335)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (32332)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (32320)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (32318)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (32329)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (32326)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (32317)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32317)Memory used [KB]: 10618
% 0.21/0.52  % (32317)Time elapsed: 0.100 s
% 0.21/0.52  % (32317)------------------------------
% 0.21/0.52  % (32317)------------------------------
% 0.21/0.53  % (32327)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (32324)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (32323)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (32330)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (32321)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (32331)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f436,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f101,f106,f113,f145,f179,f431,f435])).
% 0.21/0.54  fof(f435,plain,(
% 0.21/0.54    ~spl5_4 | spl5_2 | ~spl5_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f434,f428,f103,f142])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl5_4 <=> r2_hidden(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl5_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f428,plain,(
% 0.21/0.54    spl5_12 <=> sK1 = sK3(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.54  fof(f434,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | (spl5_2 | ~spl5_12)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f432])).
% 0.21/0.54  fof(f432,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | sK0 != sK0 | sK1 != sK1 | (spl5_2 | ~spl5_12)),
% 0.21/0.54    inference(superposition,[],[f108,f430])).
% 0.21/0.54  fof(f430,plain,(
% 0.21/0.54    sK1 = sK3(sK1,sK0) | ~spl5_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f428])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK3(sK1,X1),X1) | sK0 != X1 | sK1 != sK3(sK1,X1)) ) | spl5_2),
% 0.21/0.54    inference(superposition,[],[f105,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) != X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f49,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f34,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl5_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f103])).
% 0.21/0.54  fof(f431,plain,(
% 0.21/0.54    spl5_12 | spl5_2 | ~spl5_3 | ~spl5_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f426,f176,f110,f103,f428])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    spl5_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    spl5_9 <=> k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.54  fof(f426,plain,(
% 0.21/0.54    sK1 = sK3(sK1,sK0) | (spl5_2 | ~spl5_3 | ~spl5_9)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f425])).
% 0.21/0.54  fof(f425,plain,(
% 0.21/0.54    sK1 = sK3(sK1,sK0) | sK0 != sK0 | (spl5_2 | ~spl5_3 | ~spl5_9)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f424])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    sK1 = sK3(sK1,sK0) | sK0 != sK0 | sK1 = sK3(sK1,sK0) | (spl5_2 | ~spl5_3 | ~spl5_9)),
% 0.21/0.54    inference(resolution,[],[f410,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(sK1,X0),X0) | sK0 != X0 | sK1 = sK3(sK1,X0)) ) | spl5_2),
% 0.21/0.54    inference(superposition,[],[f105,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f66])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = X0) ) | (~spl5_3 | ~spl5_9)),
% 0.21/0.54    inference(resolution,[],[f400,f190])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl5_3 | ~spl5_9)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl5_3 | ~spl5_9)),
% 0.21/0.54    inference(resolution,[],[f184,f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,k1_xboole_0)) ) | ~spl5_3),
% 0.21/0.54    inference(superposition,[],[f96,f112])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f110])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f58,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl5_9),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f181])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,sK0)) ) | ~spl5_9),
% 0.21/0.54    inference(superposition,[],[f62,f178])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(sK0,sK0) | ~spl5_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f176])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.54  fof(f400,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0) | sK1 = X0) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f131,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f47,f66])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK0)) ) | ~spl5_3),
% 0.21/0.54    inference(superposition,[],[f94,f112])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f60,f37])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    spl5_9 | ~spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f169,f110,f176])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(sK0,sK0) | ~spl5_3),
% 0.21/0.54    inference(backward_demodulation,[],[f112,f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_3),
% 0.21/0.55    inference(forward_demodulation,[],[f124,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f30,f37])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) | ~spl5_3),
% 0.21/0.55    inference(superposition,[],[f68,f112])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f35,f37,f37])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    spl5_4 | spl5_1 | ~spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f116,f110,f98,f142])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl5_1 <=> k1_xboole_0 = sK0),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0) | ~spl5_3),
% 0.21/0.55    inference(superposition,[],[f112,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f52,f37,f66])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f70,f110])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.55    inference(definition_unfolding,[],[f26,f37,f66])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f20])).
% 0.21/0.55  fof(f20,conjecture,(
% 0.21/0.55    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ~spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f69,f103])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.55    inference(definition_unfolding,[],[f28,f66])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    sK0 != k1_tarski(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ~spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f27,f98])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (32329)------------------------------
% 0.21/0.55  % (32329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32329)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (32329)Memory used [KB]: 10874
% 0.21/0.55  % (32329)Time elapsed: 0.127 s
% 0.21/0.55  % (32329)------------------------------
% 0.21/0.55  % (32329)------------------------------
% 0.21/0.55  % (32306)Success in time 0.187 s
%------------------------------------------------------------------------------
