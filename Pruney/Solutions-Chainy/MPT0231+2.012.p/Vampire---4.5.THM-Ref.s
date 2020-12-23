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
% DateTime   : Thu Dec  3 12:36:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 169 expanded)
%              Number of leaves         :   17 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 259 expanded)
%              Number of equality atoms :   56 ( 153 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f75,f103,f111,f119,f152,f179])).

fof(f179,plain,
    ( spl3_1
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl3_1
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,
    ( sK0 != sK0
    | spl3_1
    | ~ spl3_11 ),
    inference(superposition,[],[f41,f151])).

fof(f151,plain,
    ( ! [X1] : sK0 = X1
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_11
  <=> ! [X1] : sK0 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f41,plain,
    ( sK0 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f152,plain,
    ( spl3_11
    | spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f146,f116,f150,f150])).

fof(f116,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( sK0 = X0
        | sK0 = X1 )
    | ~ spl3_9 ),
    inference(resolution,[],[f127,f17])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

% (3321)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1))
        | sK0 = X0
        | sK0 = X1 )
    | ~ spl3_9 ),
    inference(superposition,[],[f35,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f28])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f119,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f114,f108,f116])).

fof(f108,plain,
    ( spl3_8
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f114,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f113,f49])).

fof(f49,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f48,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f22,f17])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f113,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(resolution,[],[f110,f22])).

fof(f110,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f111,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f106,f68,f108])).

fof(f68,plain,
    ( spl3_4
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f31,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f19,f29,f28])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f103,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f101,f72,f39])).

fof(f72,plain,
    ( spl3_5
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( sK0 = sK2
    | ~ spl3_5 ),
    inference(resolution,[],[f95,f31])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | sK2 = X0 )
    | ~ spl3_5 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | sK2 = X0
        | sK2 = X0 )
    | ~ spl3_5 ),
    inference(superposition,[],[f35,f74])).

fof(f74,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f75,plain,
    ( spl3_4
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f44,f72,f68])).

fof(f44,plain,
    ( spl3_2
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f34,f46])).

fof(f46,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f29,f29])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f44])).

fof(f30,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f15,f28,f29])).

fof(f15,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3315)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3337)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (3329)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (3316)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (3313)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (3329)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (3315)Refutation not found, incomplete strategy% (3315)------------------------------
% 0.21/0.52  % (3315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3315)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3315)Memory used [KB]: 10618
% 0.21/0.52  % (3315)Time elapsed: 0.103 s
% 0.21/0.52  % (3315)------------------------------
% 0.21/0.52  % (3315)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f42,f47,f75,f103,f111,f119,f152,f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl3_1 | ~spl3_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    $false | (spl3_1 | ~spl3_11)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    sK0 != sK0 | (spl3_1 | ~spl3_11)),
% 0.21/0.52    inference(superposition,[],[f41,f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X1] : (sK0 = X1) ) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl3_11 <=> ! [X1] : sK0 = X1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    sK0 != sK2 | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl3_1 <=> sK0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl3_11 | spl3_11 | ~spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f146,f116,f150,f150])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl3_9 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK0 = X0 | sK0 = X1) ) | ~spl3_9),
% 0.21/0.52    inference(resolution,[],[f127,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  % (3321)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) | sK0 = X0 | sK0 = X1) ) | ~spl3_9),
% 0.21/0.52    inference(superposition,[],[f35,f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f29,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f28])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl3_9 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f108,f116])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl3_8 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_8),
% 0.21/0.52    inference(forward_demodulation,[],[f113,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f48,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f22,f17])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl3_8),
% 0.21/0.52    inference(resolution,[],[f110,f22])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl3_8 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f106,f68,f108])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl3_4 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl3_4),
% 0.21/0.52    inference(superposition,[],[f31,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f29,f28])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl3_1 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f101,f72,f39])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl3_5 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    sK0 = sK2 | ~spl3_5),
% 0.21/0.52    inference(resolution,[],[f95,f31])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) | sK2 = X0) ) | ~spl3_5),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) | sK2 = X0 | sK2 = X0) ) | ~spl3_5),
% 0.21/0.52    inference(superposition,[],[f35,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl3_4 | spl3_5 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f65,f44,f72,f68])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl3_2 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f34,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f29,f29])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f44])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f28,f29])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f39])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    sK0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (3329)------------------------------
% 0.21/0.52  % (3329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3329)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (3329)Memory used [KB]: 10746
% 0.21/0.52  % (3329)Time elapsed: 0.112 s
% 0.21/0.52  % (3329)------------------------------
% 0.21/0.52  % (3329)------------------------------
% 0.21/0.52  % (3325)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (3312)Success in time 0.158 s
%------------------------------------------------------------------------------
