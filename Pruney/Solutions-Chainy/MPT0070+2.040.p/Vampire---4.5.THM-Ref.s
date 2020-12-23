%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   96 ( 148 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f37,f45,f55,f61,f81])).

fof(f81,plain,
    ( spl3_1
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f66,f20])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f14,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_8
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f61,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f56,f52,f58])).

fof(f52,plain,
    ( spl3_7
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f56,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f54,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f50,f43,f28,f52])).

fof(f28,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,
    ( spl3_5
  <=> ! [X0] :
        ( r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0)
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f50,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f44,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f38,f34,f43])).

fof(f34,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f38,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_4 ),
    inference(superposition,[],[f16,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f37,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f32,f23,f34])).

fof(f23,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f15,f25])).

fof(f25,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f10,f28])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f18])).

fof(f12,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 17:38:59 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.41  % (25005)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (25006)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (25000)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (25000)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f21,f26,f31,f37,f45,f55,f61,f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl3_1 | ~spl3_8),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_8)),
% 0.21/0.43    inference(subsumption_resolution,[],[f66,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK2) | ~spl3_8),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl3_8),
% 0.21/0.43    inference(superposition,[],[f14,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_8 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl3_8 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f56,f52,f58])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl3_7 <=> r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_7),
% 0.21/0.43    inference(resolution,[],[f54,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f52])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl3_7 | ~spl3_3 | ~spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f50,f43,f28,f52])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl3_5 <=> ! [X0] : (r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0) | ~r1_tarski(X0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0) | (~spl3_3 | ~spl3_5)),
% 0.21/0.43    inference(resolution,[],[f44,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl3_5 | ~spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f34,f43])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl3_4 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK2),k1_xboole_0) | ~r1_tarski(X0,sK1)) ) | ~spl3_4),
% 0.21/0.43    inference(superposition,[],[f16,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f34])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl3_4 | ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f23,f34])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.43    inference(resolution,[],[f15,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f23])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f10,f28])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f11,f23])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f12,f18])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (25000)------------------------------
% 0.21/0.43  % (25000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (25000)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (25000)Memory used [KB]: 10618
% 0.21/0.43  % (25000)Time elapsed: 0.006 s
% 0.21/0.43  % (25000)------------------------------
% 0.21/0.43  % (25000)------------------------------
% 0.21/0.43  % (24995)Success in time 0.073 s
%------------------------------------------------------------------------------
