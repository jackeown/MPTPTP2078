%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 325 expanded)
%              Number of leaves         :   34 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  402 ( 939 expanded)
%              Number of equality atoms :  180 ( 537 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f126,f131,f139,f148,f218,f237,f250,f294,f342,f378,f420,f799,f802,f807,f809])).

fof(f809,plain,
    ( sK0 != sK5(sK0,sK2)
    | r2_hidden(sK5(sK0,sK2),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f807,plain,
    ( spl6_4
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f803])).

fof(f803,plain,
    ( $false
    | spl6_4
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f794,f125,f798,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

% (5091)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f798,plain,
    ( sK0 = sK5(sK0,sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl6_31
  <=> sK0 = sK5(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f125,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f794,plain,
    ( r2_hidden(sK5(sK0,sK2),sK2)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl6_30
  <=> r2_hidden(sK5(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f802,plain,
    ( spl6_31
    | ~ spl6_5
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f801,f792,f128,f796])).

fof(f128,plain,
    ( spl6_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f801,plain,
    ( sK0 = sK5(sK0,sK2)
    | ~ spl6_5
    | ~ spl6_30 ),
    inference(resolution,[],[f794,f231])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl6_5 ),
    inference(resolution,[],[f229,f108])).

fof(f108,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f229,plain,
    ( ! [X8] :
        ( r2_hidden(X8,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X8,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f103,f130])).

fof(f130,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != X2 ) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f799,plain,
    ( spl6_30
    | spl6_31
    | spl6_4 ),
    inference(avatar_split_clause,[],[f790,f123,f796,f792])).

fof(f790,plain,
    ( sK0 = sK5(sK0,sK2)
    | r2_hidden(sK5(sK0,sK2),sK2)
    | spl6_4 ),
    inference(equality_resolution,[],[f497])).

fof(f497,plain,
    ( ! [X0] :
        ( sK2 != X0
        | sK0 = sK5(sK0,X0)
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl6_4 ),
    inference(superposition,[],[f125,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f420,plain,
    ( ~ spl6_1
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f111,f417])).

fof(f417,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1
    | ~ spl6_21 ),
    inference(trivial_inequality_removal,[],[f416])).

fof(f416,plain,
    ( sK1 != sK1
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f415,f377])).

fof(f377,plain,
    ( sK1 = sK2
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl6_21
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f415,plain,
    ( sK1 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f81,f111])).

fof(f81,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f45,f78,f78])).

fof(f45,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

% (5079)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f111,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f378,plain,
    ( spl6_21
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f363,f123,f110,f375])).

fof(f363,plain,
    ( sK1 = sK2
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f124,f111])).

fof(f124,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f342,plain,
    ( spl6_1
    | spl6_3
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl6_1
    | spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f121,f112,f138,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f78,f78])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f138,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_6
  <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f112,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f121,plain,
    ( k1_xboole_0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f294,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK2
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f250,plain,
    ( spl6_2
    | spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f238,f234,f247,f114])).

fof(f114,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f247,plain,
    ( spl6_13
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f234,plain,
    ( spl6_12
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f238,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_12 ),
    inference(superposition,[],[f51,f236])).

fof(f236,plain,
    ( sK0 = sK3(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f234])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f237,plain,
    ( spl6_2
    | spl6_12
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f232,f128,f234,f114])).

fof(f232,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_5 ),
    inference(resolution,[],[f231,f51])).

fof(f218,plain,
    ( ~ spl6_10
    | spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f202,f128,f123,f215])).

fof(f215,plain,
    ( spl6_10
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f202,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f92,f130])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

% (5077)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f148,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f142,f144])).

fof(f144,plain,
    ( spl6_7
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f142,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f134,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f134,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f132,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f132,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f93,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f139,plain,
    ( spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f133,f128,f136])).

fof(f133,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_5 ),
    inference(superposition,[],[f93,f130])).

fof(f131,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f82,f128])).

fof(f82,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f44,f78,f76])).

fof(f44,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f126,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f80,f123,f119])).

fof(f80,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f46,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f117,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f79,f114,f110])).

fof(f79,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f47,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (5065)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (5090)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (5087)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (5078)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (5068)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (5067)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (5069)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5070)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (5073)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (5066)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (5076)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (5093)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (5075)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (5064)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (5094)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (5094)Refutation not found, incomplete strategy% (5094)------------------------------
% 0.20/0.54  % (5094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5094)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5094)Memory used [KB]: 1663
% 0.20/0.54  % (5094)Time elapsed: 0.130 s
% 0.20/0.54  % (5094)------------------------------
% 0.20/0.54  % (5094)------------------------------
% 0.20/0.54  % (5088)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (5084)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (5082)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (5085)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (5086)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (5092)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (5063)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (5072)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (5080)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (5083)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (5087)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f810,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f117,f126,f131,f139,f148,f218,f237,f250,f294,f342,f378,f420,f799,f802,f807,f809])).
% 0.20/0.55  fof(f809,plain,(
% 0.20/0.55    sK0 != sK5(sK0,sK2) | r2_hidden(sK5(sK0,sK2),sK2) | ~r2_hidden(sK0,sK2)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f807,plain,(
% 0.20/0.55    spl6_4 | ~spl6_30 | ~spl6_31),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f803])).
% 0.20/0.55  fof(f803,plain,(
% 0.20/0.55    $false | (spl6_4 | ~spl6_30 | ~spl6_31)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f794,f125,f798,f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK5(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f67,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f68,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f74,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f38])).
% 0.20/0.55  % (5091)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f798,plain,(
% 0.20/0.55    sK0 = sK5(sK0,sK2) | ~spl6_31),
% 0.20/0.55    inference(avatar_component_clause,[],[f796])).
% 0.20/0.55  fof(f796,plain,(
% 0.20/0.55    spl6_31 <=> sK0 = sK5(sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl6_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl6_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.55  fof(f794,plain,(
% 0.20/0.55    r2_hidden(sK5(sK0,sK2),sK2) | ~spl6_30),
% 0.20/0.55    inference(avatar_component_clause,[],[f792])).
% 0.20/0.55  fof(f792,plain,(
% 0.20/0.55    spl6_30 <=> r2_hidden(sK5(sK0,sK2),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.55  fof(f802,plain,(
% 0.20/0.55    spl6_31 | ~spl6_5 | ~spl6_30),
% 0.20/0.55    inference(avatar_split_clause,[],[f801,f792,f128,f796])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    spl6_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.55  fof(f801,plain,(
% 0.20/0.55    sK0 = sK5(sK0,sK2) | (~spl6_5 | ~spl6_30)),
% 0.20/0.55    inference(resolution,[],[f794,f231])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl6_5),
% 0.20/0.55    inference(resolution,[],[f229,f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f64,f78])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    ( ! [X8] : (r2_hidden(X8,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X8,sK2)) ) | ~spl6_5),
% 0.20/0.55    inference(superposition,[],[f103,f130])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) | ~spl6_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f128])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) | ~r2_hidden(X4,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != X2) )),
% 0.20/0.55    inference(definition_unfolding,[],[f57,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f62,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(rectify,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.55  fof(f799,plain,(
% 0.20/0.55    spl6_30 | spl6_31 | spl6_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f790,f123,f796,f792])).
% 0.20/0.55  fof(f790,plain,(
% 0.20/0.55    sK0 = sK5(sK0,sK2) | r2_hidden(sK5(sK0,sK2),sK2) | spl6_4),
% 0.20/0.55    inference(equality_resolution,[],[f497])).
% 0.20/0.55  fof(f497,plain,(
% 0.20/0.55    ( ! [X0] : (sK2 != X0 | sK0 = sK5(sK0,X0) | r2_hidden(sK5(sK0,X0),X0)) ) | spl6_4),
% 0.20/0.55    inference(superposition,[],[f125,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f66,f78])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f420,plain,(
% 0.20/0.55    ~spl6_1 | ~spl6_21),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f418])).
% 0.20/0.55  fof(f418,plain,(
% 0.20/0.55    $false | (~spl6_1 | ~spl6_21)),
% 0.20/0.55    inference(subsumption_resolution,[],[f111,f417])).
% 0.20/0.55  fof(f417,plain,(
% 0.20/0.55    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | (~spl6_1 | ~spl6_21)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f416])).
% 0.20/0.55  fof(f416,plain,(
% 0.20/0.55    sK1 != sK1 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | (~spl6_1 | ~spl6_21)),
% 0.20/0.55    inference(forward_demodulation,[],[f415,f377])).
% 0.20/0.55  fof(f377,plain,(
% 0.20/0.55    sK1 = sK2 | ~spl6_21),
% 0.20/0.55    inference(avatar_component_clause,[],[f375])).
% 0.20/0.55  fof(f375,plain,(
% 0.20/0.55    spl6_21 <=> sK1 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.55  fof(f415,plain,(
% 0.20/0.55    sK1 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_1),
% 0.20/0.55    inference(forward_demodulation,[],[f81,f111])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.55    inference(definition_unfolding,[],[f45,f78,f78])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  % (5079)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.55    inference(negated_conjecture,[],[f22])).
% 0.20/0.55  fof(f22,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    spl6_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.55  fof(f378,plain,(
% 0.20/0.55    spl6_21 | ~spl6_1 | ~spl6_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f363,f123,f110,f375])).
% 0.20/0.55  fof(f363,plain,(
% 0.20/0.55    sK1 = sK2 | (~spl6_1 | ~spl6_4)),
% 0.20/0.55    inference(forward_demodulation,[],[f124,f111])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f342,plain,(
% 0.20/0.55    spl6_1 | spl6_3 | ~spl6_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f335])).
% 0.20/0.55  fof(f335,plain,(
% 0.20/0.55    $false | (spl6_1 | spl6_3 | ~spl6_6)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f121,f112,f138,f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f48,f78,f78])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f136])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    spl6_6 <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl6_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f110])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | spl6_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f119])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    spl6_3 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != sK2 | ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(sK1,sK2)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f250,plain,(
% 0.20/0.55    spl6_2 | spl6_13 | ~spl6_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f238,f234,f247,f114])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl6_2 <=> k1_xboole_0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.55  fof(f247,plain,(
% 0.20/0.55    spl6_13 <=> r2_hidden(sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    spl6_12 <=> sK0 = sK3(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl6_12),
% 0.20/0.55    inference(superposition,[],[f51,f236])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    sK0 = sK3(sK2) | ~spl6_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f234])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    spl6_2 | spl6_12 | ~spl6_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f232,f128,f234,f114])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl6_5),
% 0.20/0.55    inference(resolution,[],[f231,f51])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    ~spl6_10 | spl6_4 | ~spl6_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f202,f128,f123,f215])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    spl6_10 <=> r1_tarski(sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl6_5),
% 0.20/0.55    inference(superposition,[],[f92,f130])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f61,f76])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.55  % (5077)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    spl6_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f142,f144])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    spl6_7 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.55    inference(superposition,[],[f134,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f132,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.56  fof(f132,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)))) )),
% 0.20/0.56    inference(superposition,[],[f93,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f63,f76])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    spl6_6 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f133,f128,f136])).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_5),
% 0.20/0.56    inference(superposition,[],[f93,f130])).
% 0.20/0.56  fof(f131,plain,(
% 0.20/0.56    spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f82,f128])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))),
% 0.20/0.56    inference(definition_unfolding,[],[f44,f78,f76])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    ~spl6_3 | ~spl6_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f80,f123,f119])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.20/0.56    inference(definition_unfolding,[],[f46,f78])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f117,plain,(
% 0.20/0.56    ~spl6_1 | ~spl6_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f79,f114,f110])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.56    inference(definition_unfolding,[],[f47,f78])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (5087)------------------------------
% 0.20/0.56  % (5087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5087)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (5087)Memory used [KB]: 11129
% 0.20/0.56  % (5087)Time elapsed: 0.087 s
% 0.20/0.56  % (5087)------------------------------
% 0.20/0.56  % (5087)------------------------------
% 0.20/0.56  % (5074)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (5079)Refutation not found, incomplete strategy% (5079)------------------------------
% 0.20/0.56  % (5079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5079)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5079)Memory used [KB]: 10618
% 0.20/0.56  % (5079)Time elapsed: 0.148 s
% 0.20/0.56  % (5079)------------------------------
% 0.20/0.56  % (5079)------------------------------
% 0.20/0.56  % (5060)Success in time 0.197 s
%------------------------------------------------------------------------------
