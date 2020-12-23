%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   82 ( 112 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f24,f28,f32,f36,f65,f90,f120,f139])).

fof(f139,plain,
    ( spl3_1
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl3_1
    | ~ spl3_17 ),
    inference(resolution,[],[f119,f19])).

fof(f19,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl3_1
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( ! [X6,X8,X7] : r1_tarski(k3_xboole_0(X6,X8),k2_xboole_0(X6,X7))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_17
  <=> ! [X7,X8,X6] : r1_tarski(k3_xboole_0(X6,X8),k2_xboole_0(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f120,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f109,f87,f30,f118])).

fof(f30,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f87,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,X0),X2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f109,plain,
    ( ! [X6,X8,X7] : r1_tarski(k3_xboole_0(X6,X8),k2_xboole_0(X6,X7))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(superposition,[],[f88,f31])).

fof(f31,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f88,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,X0),X2),X0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f90,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f77,f63,f26,f87])).

fof(f26,plain,
    ( spl3_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ! [X4,X5,X3] : r1_tarski(k3_xboole_0(k3_xboole_0(X4,X3),X5),X3)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f64,f27])).

fof(f27,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f64,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f56,f34,f22,f63])).

fof(f22,plain,
    ( spl3_2
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f34,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f35,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
        | r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f36,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f32,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f28,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f26])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f24,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f17])).

fof(f11,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (4847)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (4843)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (4847)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f20,f24,f28,f32,f36,f65,f90,f120,f139])).
% 0.21/0.42  fof(f139,plain,(
% 0.21/0.42    spl3_1 | ~spl3_17),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_17)),
% 0.21/0.42    inference(resolution,[],[f119,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    spl3_1 <=> r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,X8),k2_xboole_0(X6,X7))) ) | ~spl3_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f118])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    spl3_17 <=> ! [X7,X8,X6] : r1_tarski(k3_xboole_0(X6,X8),k2_xboole_0(X6,X7))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    spl3_17 | ~spl3_4 | ~spl3_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f109,f87,f30,f118])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl3_13 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,X0),X2),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,X8),k2_xboole_0(X6,X7))) ) | (~spl3_4 | ~spl3_13)),
% 0.21/0.42    inference(superposition,[],[f88,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,X0),X2),X0)) ) | ~spl3_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f87])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl3_13 | ~spl3_3 | ~spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f77,f63,f26,f87])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl3_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl3_9 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(k3_xboole_0(X4,X3),X5),X3)) ) | (~spl3_3 | ~spl3_9)),
% 0.21/0.42    inference(superposition,[],[f64,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f26])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0)) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f63])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl3_9 | ~spl3_2 | ~spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f56,f34,f22,f63])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    spl3_2 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl3_5 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0)) ) | (~spl3_2 | ~spl3_5)),
% 0.21/0.42    inference(resolution,[],[f35,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f22])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f34])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f26])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f22])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f11,f17])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ~r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) => ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ~r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (4847)------------------------------
% 0.21/0.43  % (4847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (4847)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (4847)Memory used [KB]: 10618
% 0.21/0.43  % (4847)Time elapsed: 0.006 s
% 0.21/0.43  % (4847)------------------------------
% 0.21/0.43  % (4847)------------------------------
% 0.21/0.43  % (4850)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (4834)Success in time 0.071 s
%------------------------------------------------------------------------------
