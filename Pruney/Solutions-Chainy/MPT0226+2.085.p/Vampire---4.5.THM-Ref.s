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
% DateTime   : Thu Dec  3 12:36:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  87 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 221 expanded)
%              Number of equality atoms :   40 (  93 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f35,f43,f48,f63,f67,f75,f81])).

fof(f81,plain,
    ( ~ spl2_5
    | ~ spl2_9
    | ~ spl2_10
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_10
    | spl2_11 ),
    inference(subsumption_resolution,[],[f79,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_10
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f79,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | ~ spl2_5
    | ~ spl2_9
    | spl2_11 ),
    inference(forward_demodulation,[],[f77,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_9
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f77,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_5
    | spl2_11 ),
    inference(resolution,[],[f74,f34])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f74,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_11
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f75,plain,
    ( ~ spl2_11
    | spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f59,f46,f41,f21,f17,f73])).

fof(f17,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f21,plain,
    ( spl2_2
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f46,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( X0 = X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f50,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f18,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f51,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f47,f22])).

fof(f22,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f46])).

fof(f50,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(superposition,[],[f42,f22])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f41])).

fof(f67,plain,
    ( spl2_10
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f58,f46,f21,f17,f65])).

fof(f58,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f22,f56])).

fof(f63,plain,
    ( spl2_9
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f56,f46,f21,f17,f61])).

fof(f48,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f13,f46])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f43,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f12,f41])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f35,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f10,f33])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f23,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f7,f21])).

fof(f7,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f19,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f8,f17])).

fof(f8,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (22782)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (22783)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (22783)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f19,f23,f35,f43,f48,f63,f67,f75,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~spl2_5 | ~spl2_9 | ~spl2_10 | spl2_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    $false | (~spl2_5 | ~spl2_9 | ~spl2_10 | spl2_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f79,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl2_10 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) | (~spl2_5 | ~spl2_9 | spl2_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f77,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    k1_xboole_0 = k1_tarski(sK0) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_9 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | (~spl2_5 | spl2_11)),
% 0.21/0.47    inference(resolution,[],[f74,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) ) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl2_5 <=> ! [X1,X0] : (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k1_tarski(sK1)) | spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_11 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~spl2_11 | spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f46,f41,f21,f17,f73])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    spl2_1 <=> sK0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    spl2_2 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl2_8 <=> ! [X1,X0] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(backward_demodulation,[],[f50,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k1_xboole_0 = k1_tarski(sK0) | (spl2_1 | ~spl2_2 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f51,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    sK0 != sK1 | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f17])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK1 | (~spl2_2 | ~spl2_8)),
% 0.21/0.47    inference(superposition,[],[f47,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f21])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k1_xboole_0 != k1_tarski(sK0) | ~r2_hidden(sK0,k1_tarski(sK1)) | (~spl2_2 | ~spl2_7)),
% 0.21/0.47    inference(superposition,[],[f42,f22])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl2_10 | spl2_1 | ~spl2_2 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f46,f21,f17,f65])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_8)),
% 0.21/0.47    inference(backward_demodulation,[],[f22,f56])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_9 | spl2_1 | ~spl2_2 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f46,f21,f17,f61])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f46])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f12,f41])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f33])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f7,f21])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f8,f17])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    sK0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22783)------------------------------
% 0.21/0.47  % (22783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22783)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22783)Memory used [KB]: 10618
% 0.21/0.47  % (22783)Time elapsed: 0.053 s
% 0.21/0.47  % (22783)------------------------------
% 0.21/0.47  % (22783)------------------------------
% 0.21/0.47  % (22775)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (22773)Success in time 0.118 s
%------------------------------------------------------------------------------
