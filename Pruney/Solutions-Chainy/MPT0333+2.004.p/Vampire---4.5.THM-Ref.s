%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 (  90 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f29,f33,f41,f69,f309,f347])).

fof(f347,plain,
    ( spl4_1
    | ~ spl4_6
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl4_1
    | ~ spl4_6
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f20,f338])).

fof(f338,plain,
    ( ! [X6,X8,X7,X9] : k2_zfmisc_1(k2_tarski(X6,X9),k2_tarski(X7,X8)) = k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X8),k4_tarski(X9,X7),k4_tarski(X9,X8))
    | ~ spl4_6
    | ~ spl4_24 ),
    inference(superposition,[],[f308,f40])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f308,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X4),k4_tarski(X3,X5)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)),k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl4_24
  <=> ! [X1,X3,X5,X0,X2,X4] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X4),k4_tarski(X3,X5)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)),k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f20,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl4_1
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f309,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f70,f67,f31,f307])).

fof(f31,plain,
    ( spl4_4
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2,X4] : k2_enumset1(X3,X4,k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_xboole_0(k2_tarski(X3,X4),k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f70,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X4),k4_tarski(X3,X5)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)),k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)))
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(superposition,[],[f68,f32])).

fof(f32,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f68,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_enumset1(X3,X4,k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_xboole_0(k2_tarski(X3,X4),k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f46,f31,f27,f67])).

fof(f27,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f46,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_enumset1(X3,X4,k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_xboole_0(k2_tarski(X3,X4),k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f28,f32])).

fof(f28,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f41,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f14,f39])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(f33,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f29,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f18])).

fof(f10,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (18675)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.43  % (18675)Refutation not found, incomplete strategy% (18675)------------------------------
% 0.20/0.43  % (18675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (18675)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (18675)Memory used [KB]: 10618
% 0.20/0.43  % (18675)Time elapsed: 0.004 s
% 0.20/0.43  % (18675)------------------------------
% 0.20/0.43  % (18675)------------------------------
% 0.20/0.47  % (18681)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (18669)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (18678)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (18669)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f21,f29,f33,f41,f69,f309,f347])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    spl4_1 | ~spl4_6 | ~spl4_24),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f346])).
% 0.20/0.49  fof(f346,plain,(
% 0.20/0.49    $false | (spl4_1 | ~spl4_6 | ~spl4_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f20,f338])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X9] : (k2_zfmisc_1(k2_tarski(X6,X9),k2_tarski(X7,X8)) = k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X8),k4_tarski(X9,X7),k4_tarski(X9,X8))) ) | (~spl4_6 | ~spl4_24)),
% 0.20/0.49    inference(superposition,[],[f308,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) ) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    spl4_6 <=> ! [X1,X0,X2] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X4),k4_tarski(X3,X5)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)),k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)))) ) | ~spl4_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f307])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    spl4_24 <=> ! [X1,X3,X5,X0,X2,X4] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X4),k4_tarski(X3,X5)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)),k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    spl4_1 <=> k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    spl4_24 | ~spl4_4 | ~spl4_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f70,f67,f31,f307])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    spl4_4 <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl4_9 <=> ! [X1,X3,X0,X2,X4] : k2_enumset1(X3,X4,k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_xboole_0(k2_tarski(X3,X4),k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X4),k4_tarski(X3,X5)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)),k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)))) ) | (~spl4_4 | ~spl4_9)),
% 0.20/0.49    inference(superposition,[],[f68,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) ) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f31])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k2_enumset1(X3,X4,k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_xboole_0(k2_tarski(X3,X4),k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))) ) | ~spl4_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl4_9 | ~spl4_3 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f31,f27,f67])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k2_enumset1(X3,X4,k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_xboole_0(k2_tarski(X3,X4),k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))) ) | (~spl4_3 | ~spl4_4)),
% 0.20/0.49    inference(superposition,[],[f28,f32])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f27])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f39])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f12,f31])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f16,f27])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f10,f18])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (18669)------------------------------
% 0.20/0.50  % (18669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18669)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (18669)Memory used [KB]: 6524
% 0.20/0.50  % (18669)Time elapsed: 0.051 s
% 0.20/0.50  % (18669)------------------------------
% 0.20/0.50  % (18669)------------------------------
% 0.20/0.50  % (18667)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (18663)Success in time 0.137 s
%------------------------------------------------------------------------------
