%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 110 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 282 expanded)
%              Number of equality atoms :   34 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f55,f67,f84,f94])).

fof(f94,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f87,f79])).

fof(f79,plain,
    ( r1_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f20,f41])).

fof(f41,plain,
    ( k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f87,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(sK0,sK0,X0),sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f49,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f84,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f79,f70])).

fof(f70,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(X0,X0,sK1),sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f68,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f68,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(sK1,sK1,X0),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f67,plain,
    ( spl3_1
    | spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_1
    | spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f65,f40])).

fof(f40,plain,
    ( k1_enumset1(sK0,sK0,sK1) != k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f65,plain,
    ( k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl3_2
    | spl3_3 ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f57,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK2)
        | k1_enumset1(X4,X4,sK1) = k4_xboole_0(k1_enumset1(X4,X4,sK1),sK2) )
    | spl3_2 ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X0) = k4_xboole_0(k1_enumset1(X2,X2,X0),X1) ) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f55,plain,
    ( ~ spl3_1
    | spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f27,f43,f48,f39])).

fof(f27,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_enumset1(sK0,sK0,sK1) != k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f19,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f51,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f48,f39])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f17,f22,f22])).

fof(f17,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f28,f43,f39])).

fof(f28,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f18,f22,f22])).

fof(f18,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (14046)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.45  % (14038)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (14044)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (14046)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f46,f51,f55,f67,f84,f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    $false | (~spl3_1 | ~spl3_3)),
% 0.21/0.45    inference(resolution,[],[f87,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl3_1),
% 0.21/0.45    inference(superposition,[],[f20,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_1 <=> k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(k1_enumset1(sK0,sK0,X0),sK2)) ) | ~spl3_3),
% 0.21/0.45    inference(resolution,[],[f49,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f26,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    r2_hidden(sK0,sK2) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl3_3 <=> r2_hidden(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f79,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(k1_enumset1(X0,X0,sK1),sK2)) ) | ~spl3_2),
% 0.21/0.45    inference(superposition,[],[f68,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f22,f22])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(k1_enumset1(sK1,sK1,X0),sK2)) ) | ~spl3_2),
% 0.21/0.45    inference(resolution,[],[f44,f32])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    r2_hidden(sK1,sK2) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_2 <=> r2_hidden(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl3_1 | spl3_2 | spl3_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    $false | (spl3_1 | spl3_2 | spl3_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f65,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK0,sK1) != k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) | (spl3_2 | spl3_3)),
% 0.21/0.45    inference(resolution,[],[f57,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f48])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X4] : (r2_hidden(X4,sK2) | k1_enumset1(X4,X4,sK1) = k4_xboole_0(k1_enumset1(X4,X4,sK1),sK2)) ) | spl3_2),
% 0.21/0.45    inference(resolution,[],[f52,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK2) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f43])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k1_enumset1(X2,X2,X0) = k4_xboole_0(k1_enumset1(X2,X2,X0),X1)) )),
% 0.21/0.45    inference(resolution,[],[f31,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f25,f22])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ~spl3_1 | spl3_3 | spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f43,f48,f39])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_enumset1(sK0,sK0,sK1) != k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.21/0.45    inference(definition_unfolding,[],[f19,f22,f22])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.45    inference(nnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl3_1 | ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f48,f39])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2) | k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.21/0.45    inference(definition_unfolding,[],[f17,f22,f22])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl3_1 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f43,f39])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK2) | k1_enumset1(sK0,sK0,sK1) = k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f22,f22])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (14046)------------------------------
% 0.21/0.45  % (14046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (14046)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (14046)Memory used [KB]: 6140
% 0.21/0.45  % (14046)Time elapsed: 0.008 s
% 0.21/0.45  % (14046)------------------------------
% 0.21/0.45  % (14046)------------------------------
% 0.21/0.45  % (14026)Success in time 0.1 s
%------------------------------------------------------------------------------
