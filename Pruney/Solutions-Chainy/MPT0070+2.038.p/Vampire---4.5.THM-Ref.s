%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 111 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 230 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f110,f125,f130,f976,f1425])).

fof(f1425,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f1424])).

fof(f1424,plain,
    ( $false
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f1421,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f47,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

% (27615)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f1421,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f124,f1419])).

fof(f1419,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f1418,f19])).

fof(f1418,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f1381,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1381,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f118,f975])).

fof(f975,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl3_10
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f112,f19])).

fof(f112,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)
    | ~ spl3_4 ),
    inference(superposition,[],[f31,f109])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f124,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f976,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f150,f127,f973])).

fof(f127,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f150,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f141,f19])).

fof(f141,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f28,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f130,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f38,f127])).

fof(f38,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f40,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f125,plain,
    ( ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f54,f43,f122])).

fof(f43,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f110,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f33,f107])).

fof(f33,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f35,f26])).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f46,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.43  % (27620)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.45  % (27613)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (27620)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f1477,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f36,f41,f46,f110,f125,f130,f976,f1425])).
% 0.22/0.47  fof(f1425,plain,(
% 0.22/0.47    ~spl3_4 | spl3_5 | ~spl3_10),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f1424])).
% 0.22/0.47  fof(f1424,plain,(
% 0.22/0.47    $false | (~spl3_4 | spl3_5 | ~spl3_10)),
% 0.22/0.47    inference(subsumption_resolution,[],[f1421,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f47,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.47    inference(superposition,[],[f20,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.47  % (27615)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  fof(f1421,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_4 | spl3_5 | ~spl3_10)),
% 0.22/0.47    inference(backward_demodulation,[],[f124,f1419])).
% 0.22/0.47  fof(f1419,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f1418,f19])).
% 0.22/0.47  fof(f1418,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_4 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f1381,f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f107])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f1381,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_10)),
% 0.22/0.47    inference(superposition,[],[f118,f975])).
% 0.22/0.47  fof(f975,plain,(
% 0.22/0.47    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f973])).
% 0.22/0.47  fof(f973,plain,(
% 0.22/0.47    spl3_10 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0)) ) | ~spl3_4),
% 0.22/0.47    inference(forward_demodulation,[],[f112,f19])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ) | ~spl3_4),
% 0.22/0.47    inference(superposition,[],[f31,f109])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f27,f21,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f122])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f976,plain,(
% 0.22/0.47    spl3_10 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f150,f127,f973])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_6),
% 0.22/0.47    inference(forward_demodulation,[],[f141,f19])).
% 0.22/0.47  fof(f141,plain,(
% 0.22/0.47    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_6),
% 0.22/0.47    inference(superposition,[],[f28,f129])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f127])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f22,f21])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    spl3_6 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f60,f38,f127])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f40,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f23,f21])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    ~spl3_5 | spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f54,f43,f122])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_3),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f45,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f21])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f43])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    spl3_4 | ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f50,f33,f107])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f35,f26])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f33])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ~spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f43])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f38])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    r1_xboole_0(sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f33])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (27620)------------------------------
% 0.22/0.47  % (27620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (27620)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (27620)Memory used [KB]: 11641
% 0.22/0.47  % (27620)Time elapsed: 0.067 s
% 0.22/0.47  % (27620)------------------------------
% 0.22/0.47  % (27620)------------------------------
% 0.22/0.47  % (27604)Success in time 0.114 s
%------------------------------------------------------------------------------
