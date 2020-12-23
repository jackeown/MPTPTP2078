%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 154 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 217 expanded)
%              Number of equality atoms :   49 ( 126 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f144,f178,f308,f347,f466])).

fof(f466,plain,
    ( spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f464,f239])).

fof(f239,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f34,f233])).

fof(f233,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f104,f58])).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f104,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f464,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f307,f463])).

fof(f463,plain,
    ( ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f449,f98])).

fof(f98,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = X9 ),
    inference(backward_demodulation,[],[f75,f88])).

fof(f88,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f75,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9)))) = X9 ),
    inference(superposition,[],[f37,f36])).

fof(f449,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f42,f346])).

fof(f346,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl3_7
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f307,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f347,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f243,f175,f344])).

fof(f175,plain,
    ( spl3_4
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f243,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f177,f233])).

fof(f177,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f308,plain,
    ( ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f59,f49,f305])).

fof(f49,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f51,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f178,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f148,f141,f175])).

fof(f141,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f148,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f143])).

fof(f143,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f64,f44,f141])).

fof(f44,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f52,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f49])).

fof(f33,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f47,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (17562)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.44  % (17562)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f477,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f47,f52,f144,f178,f308,f347,f466])).
% 0.20/0.44  fof(f466,plain,(
% 0.20/0.44    spl3_6 | ~spl3_7),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f465])).
% 0.20/0.44  fof(f465,plain,(
% 0.20/0.44    $false | (spl3_6 | ~spl3_7)),
% 0.20/0.44    inference(subsumption_resolution,[],[f464,f239])).
% 0.20/0.44  fof(f239,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.44    inference(backward_demodulation,[],[f34,f233])).
% 0.20/0.44  fof(f233,plain,(
% 0.20/0.44    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.20/0.44    inference(superposition,[],[f104,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(superposition,[],[f37,f34])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f25,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 0.20/0.44    inference(superposition,[],[f39,f34])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f28,f26])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f21,f26])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.44  fof(f464,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_6 | ~spl3_7)),
% 0.20/0.44    inference(backward_demodulation,[],[f307,f463])).
% 0.20/0.44  fof(f463,plain,(
% 0.20/0.44    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ) | ~spl3_7),
% 0.20/0.44    inference(forward_demodulation,[],[f449,f98])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = X9) )),
% 0.20/0.44    inference(backward_demodulation,[],[f75,f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 0.20/0.44    inference(superposition,[],[f38,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f24,f26,f26])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f27,f26])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9)))) = X9) )),
% 0.20/0.44    inference(superposition,[],[f37,f36])).
% 0.20/0.44  fof(f449,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) ) | ~spl3_7),
% 0.20/0.44    inference(superposition,[],[f42,f346])).
% 0.20/0.44  fof(f346,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f344])).
% 0.20/0.44  fof(f344,plain,(
% 0.20/0.44    spl3_7 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f32,f26])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.44  fof(f307,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | spl3_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f305])).
% 0.20/0.44  fof(f305,plain,(
% 0.20/0.44    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.44  fof(f347,plain,(
% 0.20/0.44    spl3_7 | ~spl3_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f243,f175,f344])).
% 0.20/0.44  fof(f175,plain,(
% 0.20/0.44    spl3_4 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.44  fof(f243,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.20/0.44    inference(backward_demodulation,[],[f177,f233])).
% 0.20/0.44  fof(f177,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f175])).
% 0.20/0.44  fof(f308,plain,(
% 0.20/0.44    ~spl3_6 | spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f59,f49,f305])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | spl3_2),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f51,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f31,f26])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f49])).
% 0.20/0.45  fof(f178,plain,(
% 0.20/0.45    spl3_4 | ~spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f148,f141,f175])).
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    spl3_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f148,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_3),
% 0.20/0.45    inference(superposition,[],[f38,f143])).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f141])).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    spl3_3 | ~spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f64,f44,f141])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f46,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f30,f26])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f44])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ~spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f33,f49])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.45    inference(definition_unfolding,[],[f19,f26])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.45    inference(negated_conjecture,[],[f12])).
% 0.20/0.45  fof(f12,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f20,f44])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    r1_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (17562)------------------------------
% 0.20/0.45  % (17562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (17562)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (17562)Memory used [KB]: 10874
% 0.20/0.45  % (17562)Time elapsed: 0.049 s
% 0.20/0.45  % (17562)------------------------------
% 0.20/0.45  % (17562)------------------------------
% 0.20/0.45  % (17546)Success in time 0.094 s
%------------------------------------------------------------------------------
