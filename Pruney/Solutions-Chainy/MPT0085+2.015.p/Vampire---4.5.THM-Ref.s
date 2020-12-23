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
% DateTime   : Thu Dec  3 12:31:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 132 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f42,f61,f76,f84])).

fof(f84,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f29,f82])).

fof(f82,plain,
    ( ! [X1] : k3_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k3_xboole_0(sK0,X1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f79,f51])).

fof(f51,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f33,f37])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f33,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( ! [X1] : k3_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f60,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_10
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f29,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f76,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f54,f40,f22,f73])).

fof(f22,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f54,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f24,f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f24,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f20,f59])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f38,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f30,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

% (31916)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f11,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (31904)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (31910)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (31906)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (31906)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f42,f61,f76,f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_10),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f83])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(subsumption_resolution,[],[f29,f82])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ( ! [X1] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k3_xboole_0(sK0,X1)) ) | (~spl3_3 | ~spl3_4 | ~spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f79,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_3 | ~spl3_4)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f33,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl3_4 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl3_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X1] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(superposition,[],[f60,f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl3_10 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl3_8 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) | spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    spl3_2 <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl3_10 | ~spl3_1 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f54,f40,f22,f73])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl3_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_5)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f24,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f22])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f59])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f32])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f27])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  % (31916)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f22])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (31906)------------------------------
% 0.22/0.47  % (31906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (31906)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (31906)Memory used [KB]: 6140
% 0.22/0.47  % (31906)Time elapsed: 0.052 s
% 0.22/0.47  % (31906)------------------------------
% 0.22/0.47  % (31906)------------------------------
% 0.22/0.47  % (31902)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (31900)Success in time 0.113 s
%------------------------------------------------------------------------------
