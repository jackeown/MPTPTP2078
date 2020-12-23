%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:48 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   36 (  61 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 156 expanded)
%              Number of equality atoms :   54 ( 112 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f45,f54,f60,f67])).

fof(f67,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f31,f26,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f26,plain,
    ( sK2 != sK5
    | spl6_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl6_3
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f31,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl6_4
  <=> k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f60,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f44,f22,f12])).

fof(f22,plain,
    ( sK1 != sK4
    | spl6_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl6_2
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f44,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_5
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f54,plain,
    ( spl6_1
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl6_1
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f18,f44,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,
    ( sK0 != sK3
    | spl6_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl6_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f45,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f37,f29,f42])).

fof(f37,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4)
    | ~ spl6_4 ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2)
        | k4_tarski(sK3,sK4) = X0 )
    | ~ spl6_4 ),
    inference(superposition,[],[f11,f31])).

fof(f32,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f9,f13,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f9,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f27,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f10,f24,f20,f16])).

fof(f10,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
