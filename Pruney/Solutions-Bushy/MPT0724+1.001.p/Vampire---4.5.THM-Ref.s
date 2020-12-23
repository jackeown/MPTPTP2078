%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0724+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:32 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 662 expanded)
%              Number of leaves         :   29 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          :  406 (4038 expanded)
%              Number of equality atoms :  135 (2153 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f72,f77,f82,f87,f105,f110,f115,f120,f133,f138,f143,f152,f334,f385,f422,f453,f490])).

fof(f490,plain,
    ( ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f463,f52])).

fof(f52,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f463,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl7_22 ),
    inference(superposition,[],[f187,f452])).

fof(f452,plain,
    ( sK3 = sK5(k2_enumset1(sK1,sK4,sK3,sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl7_22
  <=> sK3 = sK5(k2_enumset1(sK1,sK4,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f187,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK5(k2_enumset1(X1,X2,X3,X0))) ),
    inference(unit_resulting_resolution,[],[f176,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f6,f12])).

fof(f12,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f176,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X2,X3,X0)) ),
    inference(unit_resulting_resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X3,X1] :
      ( ~ sP0(X6,X1,X2,X3,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X0 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK6(X0,X1,X2,X3,X4) != X0
              & sK6(X0,X1,X2,X3,X4) != X1
              & sK6(X0,X1,X2,X3,X4) != X2
              & sK6(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4),X4) )
          & ( sK6(X0,X1,X2,X3,X4) = X0
            | sK6(X0,X1,X2,X3,X4) = X1
            | sK6(X0,X1,X2,X3,X4) = X2
            | sK6(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK6(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f17])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK6(X0,X1,X2,X3,X4) != X0
            & sK6(X0,X1,X2,X3,X4) != X1
            & sK6(X0,X1,X2,X3,X4) != X2
            & sK6(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4),X4) )
        & ( sK6(X0,X1,X2,X3,X4) = X0
          | sK6(X0,X1,X2,X3,X4) = X1
          | sK6(X0,X1,X2,X3,X4) = X2
          | sK6(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK6(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f7,f8])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f453,plain,
    ( spl7_22
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f440,f60,f55,f45,f450])).

fof(f45,plain,
    ( spl7_1
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f55,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f60,plain,
    ( spl7_4
  <=> r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f440,plain,
    ( sK3 = sK5(k2_enumset1(sK1,sK4,sK3,sK2))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f57,f350])).

fof(f350,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK4)
        | sK5(k2_enumset1(sK1,sK4,X4,sK2)) = X4 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(superposition,[],[f185,f340])).

fof(f340,plain,
    ( ! [X0] :
        ( sK4 = sK5(k2_enumset1(sK1,sK4,X0,sK2))
        | sK5(k2_enumset1(sK1,sK4,X0,sK2)) = X0 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f297,f62])).

fof(f62,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f297,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | sK5(k2_enumset1(sK1,X4,X5,sK2)) = X5
        | sK5(k2_enumset1(sK1,X4,X5,sK2)) = X4 )
    | ~ spl7_1 ),
    inference(superposition,[],[f183,f271])).

fof(f271,plain,
    ( ! [X24,X25] :
        ( sK1 = sK5(k2_enumset1(sK1,X24,X25,sK2))
        | sK5(k2_enumset1(sK1,X24,X25,sK2)) = X25
        | sK5(k2_enumset1(sK1,X24,X25,sK2)) = X24 )
    | ~ spl7_1 ),
    inference(resolution,[],[f235,f47])).

fof(f47,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f235,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X3)
      | sK5(k2_enumset1(X0,X1,X2,X3)) = X0
      | sK5(k2_enumset1(X0,X1,X2,X3)) = X2
      | sK5(k2_enumset1(X0,X1,X2,X3)) = X1 ) ),
    inference(superposition,[],[f181,f229])).

fof(f229,plain,(
    ! [X2,X0,X3,X1] :
      ( sK5(k2_enumset1(X0,X1,X2,X3)) = X3
      | sK5(k2_enumset1(X0,X1,X2,X3)) = X0
      | sK5(k2_enumset1(X0,X1,X2,X3)) = X2
      | sK5(k2_enumset1(X0,X1,X2,X3)) = X1 ) ),
    inference(resolution,[],[f182,f191])).

fof(f191,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X3,X2,X0,X4))
      | X1 = X2
      | X1 = X3
      | X0 = X1
      | X1 = X4 ) ),
    inference(resolution,[],[f26,f42])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | X0 = X6 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(sK5(k2_enumset1(X0,X1,X2,X3)),k2_enumset1(X0,X1,X2,X3)) ),
    inference(unit_resulting_resolution,[],[f173,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(unit_resulting_resolution,[],[f42,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2,X6,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK5(k2_enumset1(X0,X1,X2,X3))) ),
    inference(unit_resulting_resolution,[],[f173,f43])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK5(k2_enumset1(X1,X0,X2,X3))) ),
    inference(unit_resulting_resolution,[],[f174,f43])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X0,X2,X3)) ),
    inference(unit_resulting_resolution,[],[f42,f40])).

fof(f40,plain,(
    ! [X6,X4,X0,X3,X1] :
      ( ~ sP0(X0,X1,X6,X3,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X2 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK5(k2_enumset1(X1,X2,X0,X3))) ),
    inference(unit_resulting_resolution,[],[f175,f43])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X2,X0,X3)) ),
    inference(unit_resulting_resolution,[],[f42,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X3] :
      ( ~ sP0(X0,X6,X2,X3,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X1 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f422,plain,
    ( spl7_19
    | ~ spl7_21
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f349,f60,f45,f419,f379])).

fof(f379,plain,
    ( spl7_19
  <=> ! [X1] : sK5(k2_enumset1(sK1,sK4,X1,sK2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f419,plain,
    ( spl7_21
  <=> r2_hidden(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f349,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4,sK4)
        | sK5(k2_enumset1(sK1,sK4,X3,sK2)) = X3 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(superposition,[],[f183,f340])).

fof(f385,plain,
    ( spl7_19
    | ~ spl7_20
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f347,f60,f45,f382,f379])).

fof(f382,plain,
    ( spl7_20
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f347,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,sK4)
        | sK5(k2_enumset1(sK1,sK4,X1,sK2)) = X1 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(superposition,[],[f181,f340])).

fof(f334,plain,
    ( spl7_17
    | ~ spl7_18
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f295,f45,f331,f328])).

fof(f328,plain,
    ( spl7_17
  <=> ! [X1,X0] :
        ( sK5(k2_enumset1(sK1,X0,X1,sK2)) = X1
        | sK5(k2_enumset1(sK1,X0,X1,sK2)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f331,plain,
    ( spl7_18
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,sK1)
        | sK5(k2_enumset1(sK1,X0,X1,sK2)) = X1
        | sK5(k2_enumset1(sK1,X0,X1,sK2)) = X0 )
    | ~ spl7_1 ),
    inference(superposition,[],[f181,f271])).

fof(f152,plain,
    ( ~ spl7_16
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f99,f84,f149])).

fof(f149,plain,
    ( spl7_16
  <=> r2_hidden(sK5(sK1),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f84,plain,
    ( spl7_8
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f99,plain,
    ( ~ r2_hidden(sK5(sK1),sK5(sK1))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f86,f43])).

fof(f86,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f143,plain,
    ( ~ spl7_15
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f97,f79,f140])).

fof(f140,plain,
    ( spl7_15
  <=> r2_hidden(sK5(sK4),sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f79,plain,
    ( spl7_7
  <=> r2_hidden(sK5(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f97,plain,
    ( ~ r2_hidden(sK5(sK4),sK5(sK4))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f81,f43])).

fof(f81,plain,
    ( r2_hidden(sK5(sK4),sK4)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f138,plain,
    ( ~ spl7_14
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f95,f74,f135])).

fof(f135,plain,
    ( spl7_14
  <=> r2_hidden(sK5(sK3),sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f74,plain,
    ( spl7_6
  <=> r2_hidden(sK5(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f95,plain,
    ( ~ r2_hidden(sK5(sK3),sK5(sK3))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f76,f43])).

fof(f76,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f133,plain,
    ( ~ spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f93,f69,f130])).

fof(f130,plain,
    ( spl7_13
  <=> r2_hidden(sK5(sK2),sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f69,plain,
    ( spl7_5
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f93,plain,
    ( ~ r2_hidden(sK5(sK2),sK5(sK2))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f71,f43])).

fof(f71,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f120,plain,
    ( ~ spl7_12
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f91,f60,f117])).

fof(f117,plain,
    ( spl7_12
  <=> r2_hidden(sK4,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f91,plain,
    ( ~ r2_hidden(sK4,sK5(sK1))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f62,f43])).

fof(f115,plain,
    ( ~ spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f90,f55,f112])).

fof(f112,plain,
    ( spl7_11
  <=> r2_hidden(sK3,sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f90,plain,
    ( ~ r2_hidden(sK3,sK5(sK4))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f57,f43])).

fof(f110,plain,
    ( ~ spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f89,f50,f107])).

fof(f107,plain,
    ( spl7_10
  <=> r2_hidden(sK2,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f89,plain,
    ( ~ r2_hidden(sK2,sK5(sK3))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f52,f43])).

fof(f105,plain,
    ( ~ spl7_9
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f88,f45,f102])).

fof(f102,plain,
    ( spl7_9
  <=> r2_hidden(sK1,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f88,plain,
    ( ~ r2_hidden(sK1,sK5(sK2))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f47,f43])).

fof(f87,plain,
    ( spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f67,f60,f84])).

fof(f67,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f62,f24])).

fof(f82,plain,
    ( spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f66,f55,f79])).

fof(f66,plain,
    ( r2_hidden(sK5(sK4),sK4)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f57,f24])).

fof(f77,plain,
    ( spl7_6
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f65,f50,f74])).

fof(f65,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f52,f24])).

fof(f72,plain,
    ( spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f64,f45,f69])).

fof(f64,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f47,f24])).

fof(f63,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( r2_hidden(sK4,sK1)
    & r2_hidden(sK3,sK4)
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f5,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( r2_hidden(X3,X0)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK4,sK1)
      & r2_hidden(sK3,sK4)
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(X3,X0)
      & r2_hidden(X2,X3)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( r2_hidden(X3,X0)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_ordinal1)).

fof(f58,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
