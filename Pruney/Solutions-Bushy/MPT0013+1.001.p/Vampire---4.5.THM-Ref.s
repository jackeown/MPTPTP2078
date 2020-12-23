%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0013+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:11 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f20,f24,f32,f48])).

fof(f48,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl2_1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f15,f31])).

fof(f31,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f15,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( spl2_4
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f25,f22,f18,f30])).

fof(f18,plain,
    ( spl2_2
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f22,plain,
    ( spl2_3
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f25,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f23,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f22])).

fof(f24,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f20,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f10,f18])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f16,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f9,f13])).

fof(f9,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

%------------------------------------------------------------------------------
