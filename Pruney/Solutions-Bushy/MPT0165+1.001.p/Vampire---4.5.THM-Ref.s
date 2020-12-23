%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0165+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f19,f23,f29,f34])).

fof(f34,plain,
    ( ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f18,f28])).

fof(f28,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl6_4
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f18,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl6_2
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f29,plain,
    ( ~ spl6_4
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f24,f21,f12,f26])).

fof(f12,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f21,plain,
    ( spl6_3
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f24,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f14,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f23,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f19,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f15,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

%------------------------------------------------------------------------------
