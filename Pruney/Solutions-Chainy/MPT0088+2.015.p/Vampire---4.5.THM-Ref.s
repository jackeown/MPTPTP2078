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
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  80 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 175 expanded)
%              Number of equality atoms :   30 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f41,f47,f54,f62,f80,f166])).

fof(f166,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl3_7
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_8
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f133,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_7
    | ~ spl3_12 ),
    inference(superposition,[],[f46,f78])).

fof(f78,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_12
  <=> ! [X3,X5,X4] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f46,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f71,f59,f39,f77])).

fof(f39,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f59,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f71,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X0,X2))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f40,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f62,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f56,f39,f27,f59])).

fof(f27,plain,
    ( spl3_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f56,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k4_xboole_0(k3_xboole_0(X4,X3),X5)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f40,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f54,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f48,f35,f22,f51])).

fof(f22,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f47,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f42,f31,f17,f44])).

fof(f17,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f41,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f37,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f13,f35])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f33,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f10,f22])).

fof(f10,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f17])).

fof(f11,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (4512)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (4511)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (4511)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f41,f47,f54,f62,f80,f166])).
% 0.22/0.43  fof(f166,plain,(
% 0.22/0.43    spl3_7 | ~spl3_8 | ~spl3_12),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.43  fof(f165,plain,(
% 0.22/0.43    $false | (spl3_7 | ~spl3_8 | ~spl3_12)),
% 0.22/0.43    inference(subsumption_resolution,[],[f133,f53])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f51])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl3_8 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f133,plain,(
% 0.22/0.43    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_7 | ~spl3_12)),
% 0.22/0.43    inference(superposition,[],[f46,f78])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) ) | ~spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f77])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl3_12 <=> ! [X3,X5,X4] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl3_7 <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    spl3_12 | ~spl3_6 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f71,f59,f39,f77])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl3_6 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl3_9 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X0,X2))) ) | (~spl3_6 | ~spl3_9)),
% 0.22/0.43    inference(superposition,[],[f40,f60])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) ) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f59])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    spl3_9 | ~spl3_3 | ~spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f56,f39,f27,f59])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    spl3_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k4_xboole_0(k3_xboole_0(X4,X3),X5)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.43    inference(superposition,[],[f40,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f27])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl3_8 | ~spl3_2 | ~spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f48,f35,f22,f51])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    spl3_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_5)),
% 0.22/0.43    inference(resolution,[],[f36,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f22])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f35])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ~spl3_7 | spl3_1 | ~spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f42,f31,f17,f44])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    spl3_1 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl3_4 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 0.22/0.43    inference(resolution,[],[f32,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f17])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f31])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f39])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f35])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f12,f27])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f10,f22])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f11,f17])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (4511)------------------------------
% 0.22/0.43  % (4511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (4511)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (4511)Memory used [KB]: 10618
% 0.22/0.43  % (4511)Time elapsed: 0.007 s
% 0.22/0.43  % (4511)------------------------------
% 0.22/0.43  % (4511)------------------------------
% 0.22/0.43  % (4505)Success in time 0.07 s
%------------------------------------------------------------------------------
