%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 641 expanded)
%              Number of leaves         :   21 ( 181 expanded)
%              Depth                    :   24
%              Number of atoms          :  467 (2822 expanded)
%              Number of equality atoms :  278 (1959 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f705,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f508,f587,f660,f704])).

fof(f704,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f703])).

fof(f703,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f701,f684])).

fof(f684,plain,
    ( sK1 != sK2
    | ~ spl7_1 ),
    inference(superposition,[],[f50,f681])).

fof(f681,plain,
    ( sK2 = sK4
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f680,f50])).

fof(f680,plain,
    ( sK1 = sK4
    | sK2 = sK4
    | ~ spl7_1 ),
    inference(resolution,[],[f671,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f671,plain,
    ( r2_hidden(sK4,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_1 ),
    inference(superposition,[],[f118,f144])).

fof(f144,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_1
  <=> k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f118,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f91])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f701,plain,
    ( sK1 = sK2
    | ~ spl7_1 ),
    inference(resolution,[],[f699,f120])).

fof(f120,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f91])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f699,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK2 = X0 )
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f695])).

fof(f695,plain,
    ( ! [X0] :
        ( sK2 = X0
        | sK2 = X0
        | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK2 = X0 )
    | ~ spl7_1 ),
    inference(resolution,[],[f692,f74])).

% (10863)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f692,plain,
    ( sP0(sK2,sK2,sK2,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f691,f681])).

fof(f691,plain,
    ( sP0(sK4,sK2,sK2,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f674,f687])).

fof(f687,plain,
    ( sK2 = sK3
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f686,f49])).

fof(f49,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f686,plain,
    ( sK1 = sK3
    | sK2 = sK3
    | ~ spl7_1 ),
    inference(resolution,[],[f672,f121])).

fof(f672,plain,
    ( r2_hidden(sK3,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_1 ),
    inference(superposition,[],[f120,f144])).

fof(f674,plain,
    ( sP0(sK4,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_1 ),
    inference(superposition,[],[f125,f144])).

fof(f125,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f82,f84])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f660,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f657,f619])).

fof(f619,plain,
    ( sK1 != sK2
    | ~ spl7_4 ),
    inference(superposition,[],[f50,f615])).

fof(f615,plain,
    ( sK2 = sK4
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f614,f50])).

fof(f614,plain,
    ( sK1 = sK4
    | sK2 = sK4
    | ~ spl7_4 ),
    inference(resolution,[],[f601,f121])).

fof(f601,plain,
    ( r2_hidden(sK4,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_4 ),
    inference(superposition,[],[f118,f156])).

fof(f156,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK4,sK4,sK4,sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_4
  <=> k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f657,plain,
    ( sK1 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f649,f120])).

fof(f649,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK2 = X13 )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f644])).

fof(f644,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK2 = X13
        | sK2 = X13 )
    | ~ spl7_4 ),
    inference(superposition,[],[f121,f617])).

fof(f617,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f156,f615])).

fof(f587,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f584,f547])).

fof(f547,plain,
    ( sK1 != sK2
    | ~ spl7_3 ),
    inference(superposition,[],[f49,f535])).

fof(f535,plain,
    ( sK2 = sK3
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f534,f49])).

fof(f534,plain,
    ( sK1 = sK3
    | sK2 = sK3
    | ~ spl7_3 ),
    inference(resolution,[],[f521,f121])).

fof(f521,plain,
    ( r2_hidden(sK3,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_3 ),
    inference(superposition,[],[f118,f152])).

fof(f152,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_3
  <=> k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f584,plain,
    ( sK1 = sK2
    | ~ spl7_3 ),
    inference(resolution,[],[f559,f120])).

fof(f559,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK2 = X13 )
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f528,f535])).

fof(f528,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK3 = X13 )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2))
        | sK3 = X13
        | sK3 = X13 )
    | ~ spl7_3 ),
    inference(superposition,[],[f121,f152])).

fof(f508,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f506,f50])).

fof(f506,plain,
    ( sK1 = sK4
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f505,f49])).

fof(f505,plain,
    ( sK1 = sK3
    | sK1 = sK4
    | ~ spl7_2 ),
    inference(resolution,[],[f504,f121])).

fof(f504,plain,
    ( r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK4))
    | ~ spl7_2 ),
    inference(resolution,[],[f492,f122])).

fof(f122,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f492,plain,
    ( sP0(sK1,sK4,sK3,k2_enumset1(sK3,sK3,sK3,sK4))
    | ~ spl7_2 ),
    inference(superposition,[],[f125,f482])).

fof(f482,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k2_enumset1(sK3,sK3,sK4,sK1)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f481,f68])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f481,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k1_xboole_0) = k2_enumset1(sK3,sK3,sK4,sK1)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f474,f68])).

fof(f474,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_enumset1(sK3,sK3,sK4,sK1)
    | ~ spl7_2 ),
    inference(superposition,[],[f261,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK4))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f127,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_2
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f127,plain,(
    k2_enumset1(sK1,sK1,sK1,sK2) = k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f96,plain,(
    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f48,f91,f91])).

fof(f48,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f261,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(k2_enumset1(X9,X9,X10,X11),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_enumset1(X9,X9,X10,X11)))) = k2_enumset1(X9,X10,X11,sK1)
    | ~ spl7_2 ),
    inference(superposition,[],[f95,f242])).

fof(f242,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f148,f239])).

fof(f239,plain,
    ( sK1 = sK2
    | ~ spl7_2 ),
    inference(resolution,[],[f220,f167])).

fof(f167,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f120,f148])).

fof(f220,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k1_xboole_0)
        | sK2 = X13 )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k1_xboole_0)
        | sK2 = X13
        | sK2 = X13 )
    | ~ spl7_2 ),
    inference(superposition,[],[f121,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f198,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f198,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0)
    | ~ spl7_2 ),
    inference(resolution,[],[f163,f57])).

fof(f163,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f114,f148])).

fof(f114,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f54,f91,f92])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f91])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f67,f90,f84,f92])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f85,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f157,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f126,f154,f150,f146,f142])).

fof(f126,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(resolution,[],[f96,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f51,f91,f92,f92,f91])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10854)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (10845)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (10852)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (10864)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (10854)Refutation not found, incomplete strategy% (10854)------------------------------
% 0.20/0.51  % (10854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10854)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10854)Memory used [KB]: 10618
% 0.20/0.51  % (10854)Time elapsed: 0.094 s
% 0.20/0.51  % (10854)------------------------------
% 0.20/0.51  % (10854)------------------------------
% 0.20/0.51  % (10843)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (10860)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (10857)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (10850)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (10849)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (10851)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (10842)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (10843)Refutation not found, incomplete strategy% (10843)------------------------------
% 0.20/0.53  % (10843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10843)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10843)Memory used [KB]: 1663
% 0.20/0.53  % (10843)Time elapsed: 0.118 s
% 0.20/0.53  % (10843)------------------------------
% 0.20/0.53  % (10843)------------------------------
% 0.20/0.53  % (10866)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (10858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (10846)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (10865)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (10858)Refutation not found, incomplete strategy% (10858)------------------------------
% 0.20/0.53  % (10858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10853)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (10858)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10858)Memory used [KB]: 10618
% 0.20/0.53  % (10858)Time elapsed: 0.117 s
% 0.20/0.53  % (10858)------------------------------
% 0.20/0.53  % (10858)------------------------------
% 0.20/0.54  % (10844)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (10859)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (10869)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (10855)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (10868)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (10847)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.56  % (10870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (10856)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (10862)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % (10866)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (10848)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f705,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f157,f508,f587,f660,f704])).
% 0.20/0.57  fof(f704,plain,(
% 0.20/0.57    ~spl7_1),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f703])).
% 0.20/0.57  fof(f703,plain,(
% 0.20/0.57    $false | ~spl7_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f701,f684])).
% 0.20/0.57  fof(f684,plain,(
% 0.20/0.57    sK1 != sK2 | ~spl7_1),
% 0.20/0.57    inference(superposition,[],[f50,f681])).
% 0.20/0.57  fof(f681,plain,(
% 0.20/0.57    sK2 = sK4 | ~spl7_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f680,f50])).
% 0.20/0.57  fof(f680,plain,(
% 0.20/0.57    sK1 = sK4 | sK2 = sK4 | ~spl7_1),
% 0.20/0.57    inference(resolution,[],[f671,f121])).
% 0.20/0.57  fof(f121,plain,(
% 0.20/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.57    inference(equality_resolution,[],[f107])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.57    inference(definition_unfolding,[],[f58,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f64,f84])).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(rectify,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(flattening,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(nnf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.57  fof(f671,plain,(
% 0.20/0.57    r2_hidden(sK4,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_1),
% 0.20/0.57    inference(superposition,[],[f118,f144])).
% 0.20/0.57  fof(f144,plain,(
% 0.20/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK4) | ~spl7_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f142])).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    spl7_1 <=> k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 0.20/0.57    inference(equality_resolution,[],[f117])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 0.20/0.57    inference(equality_resolution,[],[f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.57    inference(definition_unfolding,[],[f60,f91])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f41])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    sK1 != sK4),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.57    inference(negated_conjecture,[],[f23])).
% 0.20/0.57  fof(f23,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.20/0.57  fof(f701,plain,(
% 0.20/0.57    sK1 = sK2 | ~spl7_1),
% 0.20/0.57    inference(resolution,[],[f699,f120])).
% 0.20/0.57  fof(f120,plain,(
% 0.20/0.57    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 0.20/0.57    inference(equality_resolution,[],[f119])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 0.20/0.57    inference(equality_resolution,[],[f106])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.57    inference(definition_unfolding,[],[f59,f91])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f41])).
% 0.20/0.57  fof(f699,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2)) | sK2 = X0) ) | ~spl7_1),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f695])).
% 0.20/0.57  fof(f695,plain,(
% 0.20/0.57    ( ! [X0] : (sK2 = X0 | sK2 = X0 | ~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2)) | sK2 = X0) ) | ~spl7_1),
% 0.20/0.57    inference(resolution,[],[f692,f74])).
% 0.20/0.57  % (10863)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.57    inference(rectify,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.57    inference(flattening,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.57    inference(nnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.57  fof(f692,plain,(
% 0.20/0.57    sP0(sK2,sK2,sK2,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_1),
% 0.20/0.57    inference(forward_demodulation,[],[f691,f681])).
% 0.20/0.57  fof(f691,plain,(
% 0.20/0.57    sP0(sK4,sK2,sK2,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_1),
% 0.20/0.57    inference(forward_demodulation,[],[f674,f687])).
% 0.20/0.57  fof(f687,plain,(
% 0.20/0.57    sK2 = sK3 | ~spl7_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f686,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    sK1 != sK3),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f686,plain,(
% 0.20/0.57    sK1 = sK3 | sK2 = sK3 | ~spl7_1),
% 0.20/0.57    inference(resolution,[],[f672,f121])).
% 0.20/0.57  fof(f672,plain,(
% 0.20/0.57    r2_hidden(sK3,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_1),
% 0.20/0.57    inference(superposition,[],[f120,f144])).
% 0.20/0.57  fof(f674,plain,(
% 0.20/0.57    sP0(sK4,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_1),
% 0.20/0.57    inference(superposition,[],[f125,f144])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.20/0.57    inference(equality_resolution,[],[f109])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.57    inference(definition_unfolding,[],[f82,f84])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.57    inference(nnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.20/0.57    inference(definition_folding,[],[f30,f31])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.57  fof(f660,plain,(
% 0.20/0.57    ~spl7_4),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f659])).
% 0.20/0.57  fof(f659,plain,(
% 0.20/0.57    $false | ~spl7_4),
% 0.20/0.57    inference(subsumption_resolution,[],[f657,f619])).
% 0.20/0.57  fof(f619,plain,(
% 0.20/0.57    sK1 != sK2 | ~spl7_4),
% 0.20/0.57    inference(superposition,[],[f50,f615])).
% 0.20/0.57  fof(f615,plain,(
% 0.20/0.57    sK2 = sK4 | ~spl7_4),
% 0.20/0.57    inference(subsumption_resolution,[],[f614,f50])).
% 0.20/0.57  fof(f614,plain,(
% 0.20/0.57    sK1 = sK4 | sK2 = sK4 | ~spl7_4),
% 0.20/0.57    inference(resolution,[],[f601,f121])).
% 0.20/0.57  fof(f601,plain,(
% 0.20/0.57    r2_hidden(sK4,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_4),
% 0.20/0.57    inference(superposition,[],[f118,f156])).
% 0.20/0.57  fof(f156,plain,(
% 0.20/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK4,sK4,sK4,sK4) | ~spl7_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f154])).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    spl7_4 <=> k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK4,sK4,sK4,sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.57  fof(f657,plain,(
% 0.20/0.57    sK1 = sK2 | ~spl7_4),
% 0.20/0.57    inference(resolution,[],[f649,f120])).
% 0.20/0.57  fof(f649,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2)) | sK2 = X13) ) | ~spl7_4),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f644])).
% 0.20/0.57  fof(f644,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2)) | sK2 = X13 | sK2 = X13) ) | ~spl7_4),
% 0.20/0.57    inference(superposition,[],[f121,f617])).
% 0.20/0.57  fof(f617,plain,(
% 0.20/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl7_4),
% 0.20/0.57    inference(backward_demodulation,[],[f156,f615])).
% 0.20/0.57  fof(f587,plain,(
% 0.20/0.57    ~spl7_3),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f586])).
% 0.20/0.57  fof(f586,plain,(
% 0.20/0.57    $false | ~spl7_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f584,f547])).
% 0.20/0.57  fof(f547,plain,(
% 0.20/0.57    sK1 != sK2 | ~spl7_3),
% 0.20/0.57    inference(superposition,[],[f49,f535])).
% 0.20/0.57  fof(f535,plain,(
% 0.20/0.57    sK2 = sK3 | ~spl7_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f534,f49])).
% 0.20/0.57  fof(f534,plain,(
% 0.20/0.57    sK1 = sK3 | sK2 = sK3 | ~spl7_3),
% 0.20/0.57    inference(resolution,[],[f521,f121])).
% 0.20/0.57  fof(f521,plain,(
% 0.20/0.57    r2_hidden(sK3,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_3),
% 0.20/0.57    inference(superposition,[],[f118,f152])).
% 0.20/0.57  fof(f152,plain,(
% 0.20/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) | ~spl7_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f150])).
% 0.20/0.57  fof(f150,plain,(
% 0.20/0.57    spl7_3 <=> k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.57  fof(f584,plain,(
% 0.20/0.57    sK1 = sK2 | ~spl7_3),
% 0.20/0.57    inference(resolution,[],[f559,f120])).
% 0.20/0.57  fof(f559,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2)) | sK2 = X13) ) | ~spl7_3),
% 0.20/0.57    inference(forward_demodulation,[],[f528,f535])).
% 0.20/0.57  fof(f528,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2)) | sK3 = X13) ) | ~spl7_3),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f523])).
% 0.20/0.57  fof(f523,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k2_enumset1(sK1,sK1,sK1,sK2)) | sK3 = X13 | sK3 = X13) ) | ~spl7_3),
% 0.20/0.57    inference(superposition,[],[f121,f152])).
% 0.20/0.57  fof(f508,plain,(
% 0.20/0.57    ~spl7_2),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f507])).
% 0.20/0.57  fof(f507,plain,(
% 0.20/0.57    $false | ~spl7_2),
% 0.20/0.57    inference(subsumption_resolution,[],[f506,f50])).
% 0.20/0.57  fof(f506,plain,(
% 0.20/0.57    sK1 = sK4 | ~spl7_2),
% 0.20/0.57    inference(subsumption_resolution,[],[f505,f49])).
% 0.20/0.57  fof(f505,plain,(
% 0.20/0.57    sK1 = sK3 | sK1 = sK4 | ~spl7_2),
% 0.20/0.57    inference(resolution,[],[f504,f121])).
% 0.20/0.57  fof(f504,plain,(
% 0.20/0.57    r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK4)) | ~spl7_2),
% 0.20/0.57    inference(resolution,[],[f492,f122])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 0.20/0.57    inference(equality_resolution,[],[f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f492,plain,(
% 0.20/0.57    sP0(sK1,sK4,sK3,k2_enumset1(sK3,sK3,sK3,sK4)) | ~spl7_2),
% 0.20/0.57    inference(superposition,[],[f125,f482])).
% 0.20/0.57  fof(f482,plain,(
% 0.20/0.57    k2_enumset1(sK3,sK3,sK3,sK4) = k2_enumset1(sK3,sK3,sK4,sK1) | ~spl7_2),
% 0.20/0.57    inference(forward_demodulation,[],[f481,f68])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.57  fof(f481,plain,(
% 0.20/0.57    k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k1_xboole_0) = k2_enumset1(sK3,sK3,sK4,sK1) | ~spl7_2),
% 0.20/0.57    inference(forward_demodulation,[],[f474,f68])).
% 0.20/0.57  fof(f474,plain,(
% 0.20/0.57    k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_enumset1(sK3,sK3,sK4,sK1) | ~spl7_2),
% 0.20/0.57    inference(superposition,[],[f261,f159])).
% 0.20/0.57  fof(f159,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_enumset1(sK3,sK3,sK3,sK4)) | ~spl7_2),
% 0.20/0.57    inference(backward_demodulation,[],[f127,f148])).
% 0.20/0.57  fof(f148,plain,(
% 0.20/0.57    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK2) | ~spl7_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f146])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    spl7_2 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4))),
% 0.20/0.57    inference(resolution,[],[f96,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4))),
% 0.20/0.57    inference(definition_unfolding,[],[f48,f91,f91])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f261,plain,(
% 0.20/0.57    ( ! [X10,X11,X9] : (k5_xboole_0(k2_enumset1(X9,X9,X10,X11),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_enumset1(X9,X9,X10,X11)))) = k2_enumset1(X9,X10,X11,sK1)) ) | ~spl7_2),
% 0.20/0.57    inference(superposition,[],[f95,f242])).
% 0.20/0.57  fof(f242,plain,(
% 0.20/0.57    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_2),
% 0.20/0.57    inference(backward_demodulation,[],[f148,f239])).
% 0.20/0.57  fof(f239,plain,(
% 0.20/0.57    sK1 = sK2 | ~spl7_2),
% 0.20/0.57    inference(resolution,[],[f220,f167])).
% 0.20/0.57  fof(f167,plain,(
% 0.20/0.57    r2_hidden(sK1,k1_xboole_0) | ~spl7_2),
% 0.20/0.57    inference(superposition,[],[f120,f148])).
% 0.20/0.57  fof(f220,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k1_xboole_0) | sK2 = X13) ) | ~spl7_2),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f215])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    ( ! [X13] : (~r2_hidden(X13,k1_xboole_0) | sK2 = X13 | sK2 = X13) ) | ~spl7_2),
% 0.20/0.57    inference(superposition,[],[f121,f199])).
% 0.20/0.57  fof(f199,plain,(
% 0.20/0.57    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl7_2),
% 0.20/0.57    inference(forward_demodulation,[],[f198,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.57  fof(f198,plain,(
% 0.20/0.57    k2_enumset1(sK2,sK2,sK2,sK2) = k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) | ~spl7_2),
% 0.20/0.57    inference(resolution,[],[f163,f57])).
% 0.20/0.57  fof(f163,plain,(
% 0.20/0.57    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0) | ~spl7_2),
% 0.20/0.57    inference(superposition,[],[f114,f148])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 0.20/0.57    inference(equality_resolution,[],[f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f54,f91,f92])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f65,f91])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.57    inference(flattening,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.57    inference(nnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f67,f90,f84,f92])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f85,f71])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.57  fof(f157,plain,(
% 0.20/0.57    spl7_1 | spl7_2 | spl7_3 | spl7_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f126,f154,f150,f146,f142])).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK4,sK4,sK4,sK4) | k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK2) | k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK4)),
% 0.20/0.57    inference(resolution,[],[f96,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X2) = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f51,f91,f92,f92,f91])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (10866)------------------------------
% 0.20/0.57  % (10866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10866)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (10866)Memory used [KB]: 11001
% 0.20/0.57  % (10866)Time elapsed: 0.147 s
% 0.20/0.57  % (10866)------------------------------
% 0.20/0.57  % (10866)------------------------------
% 0.20/0.57  % (10872)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.57  % (10872)Refutation not found, incomplete strategy% (10872)------------------------------
% 0.20/0.57  % (10872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (10872)Memory used [KB]: 1663
% 0.20/0.57  % (10872)Time elapsed: 0.002 s
% 0.20/0.57  % (10872)------------------------------
% 0.20/0.57  % (10872)------------------------------
% 0.20/0.58  % (10841)Success in time 0.219 s
%------------------------------------------------------------------------------
