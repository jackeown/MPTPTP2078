%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :  108 ( 156 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f48,f53,f59,f83,f87])).

fof(f87,plain,
    ( spl3_1
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f82,f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_13
  <=> ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f83,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f79,f56,f51,f46,f81])).

fof(f46,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f51,plain,
    ( spl3_8
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f56,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f79,plain,
    ( ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f69,f52])).

fof(f52,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f69,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,k1_xboole_0)
        | r1_xboole_0(sK0,k4_xboole_0(X2,sK1)) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f47,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f59,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f54,f38,f25,f56])).

fof(f25,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f54,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f53,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f34,f30,f51])).

fof(f30,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f34,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f49,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f35,f31])).

fof(f31,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f35,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f48,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f40,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f36,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f20])).

fof(f13,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (9982)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (9983)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.43  % (9980)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (9980)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f48,f53,f59,f83,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl3_1 | ~spl3_13),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    $false | (spl3_1 | ~spl3_13)),
% 0.20/0.43    inference(resolution,[],[f82,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X2] : (r1_xboole_0(sK0,k4_xboole_0(X2,sK1))) ) | ~spl3_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl3_13 <=> ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f56,f51,f46,f81])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl3_7 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl3_8 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl3_9 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X2] : (r1_xboole_0(sK0,k4_xboole_0(X2,sK1))) ) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f69,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f51])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X2] : (~r1_xboole_0(X2,k1_xboole_0) | r1_xboole_0(sK0,k4_xboole_0(X2,sK1))) ) | (~spl3_7 | ~spl3_9)),
% 0.20/0.43    inference(superposition,[],[f47,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f56])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl3_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f46])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl3_9 | ~spl3_2 | ~spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f54,f38,f25,f56])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    spl3_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_5)),
% 0.20/0.43    inference(resolution,[],[f39,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f25])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f38])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl3_8 | ~spl3_3 | ~spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f49,f34,f30,f51])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl3_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_3 | ~spl3_4)),
% 0.20/0.43    inference(superposition,[],[f35,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f30])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f46])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f38])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f34])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f14,f30])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f12,f25])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f13,f20])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (9980)------------------------------
% 0.20/0.43  % (9980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (9980)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (9980)Memory used [KB]: 10618
% 0.20/0.43  % (9980)Time elapsed: 0.005 s
% 0.20/0.43  % (9980)------------------------------
% 0.20/0.43  % (9980)------------------------------
% 0.20/0.44  % (9974)Success in time 0.075 s
%------------------------------------------------------------------------------
