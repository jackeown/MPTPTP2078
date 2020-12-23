%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:08 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (  61 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 110 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f116,f153,f156])).

fof(f156,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f152,f125])).

fof(f125,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f118,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f118,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f29,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f152,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f153,plain,
    ( ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f41,f37,f150])).

fof(f37,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f39,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f116,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f32,f113])).

fof(f32,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f40,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f14,f19])).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:23:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.39  % (29306)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.40  % (29316)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.41  % (29316)Refutation found. Thanks to Tanya!
% 0.18/0.41  % SZS status Theorem for theBenchmark
% 0.18/0.41  % SZS output start Proof for theBenchmark
% 0.18/0.41  fof(f157,plain,(
% 0.18/0.41    $false),
% 0.18/0.41    inference(avatar_sat_refutation,[],[f35,f40,f116,f153,f156])).
% 0.18/0.41  fof(f156,plain,(
% 0.18/0.41    ~spl3_3 | spl3_6),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f155])).
% 0.18/0.41  fof(f155,plain,(
% 0.18/0.41    $false | (~spl3_3 | spl3_6)),
% 0.18/0.41    inference(subsumption_resolution,[],[f152,f125])).
% 0.18/0.41  fof(f125,plain,(
% 0.18/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0)))) ) | ~spl3_3),
% 0.18/0.41    inference(forward_demodulation,[],[f118,f17])).
% 0.18/0.41  fof(f17,plain,(
% 0.18/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f7])).
% 0.18/0.41  fof(f7,axiom,(
% 0.18/0.41    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.18/0.41  fof(f118,plain,(
% 0.18/0.41    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0)))) ) | ~spl3_3),
% 0.18/0.41    inference(superposition,[],[f29,f115])).
% 0.18/0.41  fof(f115,plain,(
% 0.18/0.41    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.18/0.41    inference(avatar_component_clause,[],[f113])).
% 0.18/0.41  fof(f113,plain,(
% 0.18/0.41    spl3_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.41  fof(f29,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.18/0.41    inference(definition_unfolding,[],[f23,f19,f19])).
% 0.18/0.41  fof(f19,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.18/0.41    inference(cnf_transformation,[],[f5])).
% 0.18/0.41  fof(f5,axiom,(
% 0.18/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.18/0.41  fof(f23,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f6])).
% 0.18/0.41  fof(f6,axiom,(
% 0.18/0.41    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.18/0.41  fof(f152,plain,(
% 0.18/0.41    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | spl3_6),
% 0.18/0.41    inference(avatar_component_clause,[],[f150])).
% 0.18/0.41  fof(f150,plain,(
% 0.18/0.41    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.41  fof(f153,plain,(
% 0.18/0.41    ~spl3_6 | spl3_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f41,f37,f150])).
% 0.18/0.41  fof(f37,plain,(
% 0.18/0.41    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.41  fof(f41,plain,(
% 0.18/0.41    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | spl3_2),
% 0.18/0.41    inference(unit_resulting_resolution,[],[f39,f27])).
% 0.18/0.41  fof(f27,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.18/0.41    inference(definition_unfolding,[],[f22,f19])).
% 0.18/0.41  fof(f22,plain,(
% 0.18/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.18/0.41    inference(cnf_transformation,[],[f13])).
% 0.18/0.41  fof(f13,plain,(
% 0.18/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.41    inference(nnf_transformation,[],[f1])).
% 0.18/0.41  fof(f1,axiom,(
% 0.18/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.18/0.41  fof(f39,plain,(
% 0.18/0.41    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_2),
% 0.18/0.41    inference(avatar_component_clause,[],[f37])).
% 0.18/0.41  fof(f116,plain,(
% 0.18/0.41    spl3_3 | ~spl3_1),
% 0.18/0.41    inference(avatar_split_clause,[],[f50,f32,f113])).
% 0.18/0.41  fof(f32,plain,(
% 0.18/0.41    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.41  fof(f50,plain,(
% 0.18/0.41    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.18/0.41    inference(unit_resulting_resolution,[],[f34,f28])).
% 0.18/0.41  fof(f28,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.18/0.41    inference(definition_unfolding,[],[f21,f19])).
% 0.18/0.41  fof(f21,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f13])).
% 0.18/0.41  fof(f34,plain,(
% 0.18/0.41    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.18/0.41    inference(avatar_component_clause,[],[f32])).
% 0.18/0.41  fof(f40,plain,(
% 0.18/0.41    ~spl3_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f24,f37])).
% 0.18/0.41  fof(f24,plain,(
% 0.18/0.41    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.18/0.41    inference(definition_unfolding,[],[f14,f19])).
% 0.18/0.41  fof(f14,plain,(
% 0.18/0.41    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.18/0.41    inference(cnf_transformation,[],[f12])).
% 0.18/0.41  fof(f12,plain,(
% 0.18/0.41    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.18/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.18/0.41  fof(f11,plain,(
% 0.18/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.18/0.41    introduced(choice_axiom,[])).
% 0.18/0.41  fof(f10,plain,(
% 0.18/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.18/0.41    inference(ennf_transformation,[],[f9])).
% 0.18/0.41  fof(f9,negated_conjecture,(
% 0.18/0.41    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.18/0.41    inference(negated_conjecture,[],[f8])).
% 0.18/0.41  fof(f8,conjecture,(
% 0.18/0.41    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.18/0.41  fof(f35,plain,(
% 0.18/0.41    spl3_1),
% 0.18/0.41    inference(avatar_split_clause,[],[f15,f32])).
% 0.18/0.41  fof(f15,plain,(
% 0.18/0.41    r1_xboole_0(sK0,sK1)),
% 0.18/0.41    inference(cnf_transformation,[],[f12])).
% 0.18/0.41  % SZS output end Proof for theBenchmark
% 0.18/0.41  % (29316)------------------------------
% 0.18/0.41  % (29316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.41  % (29316)Termination reason: Refutation
% 0.18/0.41  
% 0.18/0.41  % (29316)Memory used [KB]: 10618
% 0.18/0.41  % (29316)Time elapsed: 0.005 s
% 0.18/0.41  % (29316)------------------------------
% 0.18/0.41  % (29316)------------------------------
% 0.18/0.41  % (29298)Success in time 0.075 s
%------------------------------------------------------------------------------
