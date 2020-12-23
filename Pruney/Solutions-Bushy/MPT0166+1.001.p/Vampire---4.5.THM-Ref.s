%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0166+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:28 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f19,f23,f29,f34])).

fof(f34,plain,
    ( ~ spl1_2
    | spl1_4 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | ~ spl1_2
    | spl1_4 ),
    inference(unit_resulting_resolution,[],[f18,f28])).

fof(f28,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_4
  <=> k1_tarski(sK0) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f18,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl1_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f29,plain,
    ( ~ spl1_4
    | spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f24,f21,f12,f26])).

fof(f12,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f21,plain,
    ( spl1_3
  <=> ! [X1,X0] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f24,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,
    ( ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f14,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f23,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f19,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0)
   => k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

% (19525)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

%------------------------------------------------------------------------------
