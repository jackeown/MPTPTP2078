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
% DateTime   : Thu Dec  3 12:31:46 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  95 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f35,f41,f47])).

fof(f47,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f44,f40])).

fof(f40,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_6
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f44,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f17,f26])).

fof(f26,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f17,plain,
    ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl2_1
  <=> sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f41,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f36,f33,f20,f38])).

fof(f20,plain,
    ( spl2_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f36,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f35,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f27,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f11,f25])).

fof(f11,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f23,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f9,f20])).

fof(f9,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
        & r1_xboole_0(X0,X1) )
   => ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
       => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f18,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f10,f15])).

fof(f10,plain,(
    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (521)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.41  % (521)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f18,f23,f27,f35,f41,f47])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    spl2_1 | ~spl2_3 | ~spl2_6),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f46])).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    $false | (spl2_1 | ~spl2_3 | ~spl2_6)),
% 0.13/0.42    inference(subsumption_resolution,[],[f44,f40])).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_6),
% 0.13/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_6 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    sK0 != k4_xboole_0(sK0,sK1) | (spl2_1 | ~spl2_3)),
% 0.21/0.42    inference(superposition,[],[f17,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl2_3 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    spl2_1 <=> sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl2_6 | ~spl2_2 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f33,f20,f38])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    spl2_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl2_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    sK0 = k4_xboole_0(sK0,sK1) | (~spl2_2 | ~spl2_5)),
% 0.21/0.42    inference(resolution,[],[f34,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f20])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f33])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f11,f25])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f9,f20])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) & r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0 & r1_xboole_0(X0,X1)) => (sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) & r1_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0 & r1_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f10,f15])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (521)------------------------------
% 0.21/0.42  % (521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (521)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (521)Memory used [KB]: 10490
% 0.21/0.42  % (521)Time elapsed: 0.005 s
% 0.21/0.42  % (521)------------------------------
% 0.21/0.42  % (521)------------------------------
% 0.21/0.42  % (512)Success in time 0.062 s
%------------------------------------------------------------------------------
