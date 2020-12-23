%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  64 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 108 expanded)
%              Number of equality atoms :   20 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f48,f50])).

fof(f50,plain,
    ( spl2_1
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f47,f43])).

fof(f43,plain,
    ( ! [X0] : ~ r1_tarski(k2_enumset1(X0,X0,X0,sK1),sK0)
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f34,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_3
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f41,f37,f45])).

fof(f37,plain,
    ( spl2_2
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f27,f39])).

fof(f39,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f37])).

fof(f26,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f14,f25,f19,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r2_hidden(sK1,sK0)
    & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK1,sK0)
      & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (14250)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (14254)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.44  % (14254)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % (14250)Refutation not found, incomplete strategy% (14250)------------------------------
% 0.21/0.44  % (14250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (14250)Memory used [KB]: 10490
% 0.21/0.44  % (14250)Time elapsed: 0.007 s
% 0.21/0.44  % (14250)------------------------------
% 0.21/0.44  % (14250)------------------------------
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f35,f40,f48,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl2_1 | ~spl2_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    $false | (spl2_1 | ~spl2_3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f47,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_enumset1(X0,X0,X0,sK1),sK0)) ) | spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f34,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f22,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f18,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(nnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~r2_hidden(sK1,sK0) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl2_1 <=> r2_hidden(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl2_3 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl2_3 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f41,f37,f45])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_2 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_2),
% 0.21/0.44    inference(superposition,[],[f27,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f17,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f37])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.44    inference(definition_unfolding,[],[f14,f25,f19,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f16,f24])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ~r2_hidden(sK1,sK0) & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))) => (~r2_hidden(sK1,sK0) & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ~r2_hidden(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (14254)------------------------------
% 0.21/0.44  % (14254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14254)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (14254)Memory used [KB]: 10618
% 0.21/0.44  % (14254)Time elapsed: 0.008 s
% 0.21/0.44  % (14254)------------------------------
% 0.21/0.44  % (14254)------------------------------
% 0.21/0.45  % (14238)Success in time 0.089 s
%------------------------------------------------------------------------------
