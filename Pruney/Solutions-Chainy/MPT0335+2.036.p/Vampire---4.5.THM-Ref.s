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
% DateTime   : Thu Dec  3 12:43:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 128 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 280 expanded)
%              Number of equality atoms :   51 ( 130 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f62,f70,f90,f98,f161])).

fof(f161,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f160,f94,f66,f59])).

fof(f59,plain,
    ( spl4_5
  <=> k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f66,plain,
    ( spl4_6
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f94,plain,
    ( spl4_8
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f160,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f134,f73])).

fof(f73,plain,
    ( ! [X6] : k3_xboole_0(sK0,k3_xboole_0(sK1,X6)) = k3_xboole_0(sK0,X6)
    | ~ spl4_6 ),
    inference(superposition,[],[f28,f68])).

fof(f68,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f134,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_8 ),
    inference(superposition,[],[f22,f96])).

fof(f96,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f98,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f92,f85,f94])).

fof(f85,plain,
    ( spl4_7
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f92,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f87,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
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

fof(f87,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f90,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f89,f48,f43,f85])).

fof(f43,plain,
    ( spl4_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,
    ( spl4_3
  <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f82,f50])).

fof(f50,plain,
    ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f82,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f70,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f64,f53,f66])).

fof(f53,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f64,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f24,f55])).

fof(f55,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f62,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f48,f38,f59])).

fof(f38,plain,
    ( spl4_1
  <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f40,f50])).

fof(f40,plain,
    ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f56,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f53])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f48])).

fof(f34,plain,(
    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f18,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f33,f38])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f20,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (26600)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (26592)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (26596)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (26604)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (26593)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (26591)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (26595)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (26594)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (26597)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (26601)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (26595)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (26603)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f62,f70,f90,f98,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl4_5 | ~spl4_6 | ~spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f160,f94,f66,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl4_5 <=> k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl4_6 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl4_8 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) | (~spl4_6 | ~spl4_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f134,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X6] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X6)) = k3_xboole_0(sK0,X6)) ) | ~spl4_6),
% 0.21/0.50    inference(superposition,[],[f28,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_8),
% 0.21/0.50    inference(superposition,[],[f22,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl4_8 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f92,f85,f94])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl4_7 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl4_7),
% 0.21/0.50    inference(resolution,[],[f87,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    r1_tarski(k3_xboole_0(sK1,sK2),sK0) | ~spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl4_7 | ~spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f89,f48,f43,f85])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl4_2 <=> r2_hidden(sK3,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl4_3 <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    r1_tarski(k3_xboole_0(sK1,sK2),sK0) | (~spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f82,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f48])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f35,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    r2_hidden(sK3,sK0) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f43])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f21,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f23,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f27,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl4_6 | ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f53,f66])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl4_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f24,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f53])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~spl4_5 | spl4_1 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f48,f38,f59])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    spl4_1 <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2) | (spl4_1 | ~spl4_3)),
% 0.21/0.50    inference(superposition,[],[f40,f50])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f38])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f53])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f48])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f32])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f43])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    r2_hidden(sK3,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f38])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f32])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26595)------------------------------
% 0.21/0.50  % (26595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26595)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26595)Memory used [KB]: 6140
% 0.21/0.50  % (26595)Time elapsed: 0.071 s
% 0.21/0.50  % (26595)------------------------------
% 0.21/0.50  % (26595)------------------------------
% 0.21/0.51  % (26588)Success in time 0.144 s
%------------------------------------------------------------------------------
