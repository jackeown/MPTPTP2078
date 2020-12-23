%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:41 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 477 expanded)
%              Number of leaves         :   28 ( 151 expanded)
%              Depth                    :   15
%              Number of atoms          :  521 (2455 expanded)
%              Number of equality atoms :   32 ( 117 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1850,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f134,f139,f143,f219,f379,f709,f764,f1849])).

fof(f1849,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f1848])).

fof(f1848,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1847,f1328])).

fof(f1328,plain,
    ( r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f1321,f948])).

fof(f948,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f128,f808,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f100,f71])).

fof(f71,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f808,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f65,f225,f773,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f76,f71])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f773,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f138,f65,f133,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f73,f71])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f133,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f138,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f225,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f138,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f72,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f65,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
        & r2_hidden(sK1,sK0)
        & v3_ordinal1(sK1) )
      | ~ v4_ordinal1(sK0) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK0)
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK0) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK0)
            & r2_hidden(X1,sK0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK0)
            | ~ r2_hidden(X2,sK0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f128,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1321,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f138,f872,f1293,f109])).

fof(f1293,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f65,f869,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f869,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f133,f798])).

fof(f798,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f118,f765])).

fof(f765,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f123,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f118,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK5(X0,X1),X3) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ( r2_hidden(sK6(X0,X1),X0)
              & r2_hidden(sK5(X0,X1),sK6(X0,X1)) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK7(X0,X5),X0)
                & r2_hidden(X5,sK7(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f58,f61,f60,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK5(X0,X1),X3) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK5(X0,X1),X4) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f872,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f133,f799])).

fof(f799,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f119,f765])).

fof(f119,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1847,plain,
    ( ~ r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f65,f1293,f1297,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f1297,plain,
    ( ~ r1_tarski(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f869,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f764,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f762,f716])).

fof(f716,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f246,f106,f214,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f214,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f106,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f70,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f246,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f124,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f762,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f214,f717,f142])).

fof(f142,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f717,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f65,f214,f84])).

fof(f709,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f703,f578])).

fof(f578,plain,
    ( ~ r1_ordinal1(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f65,f296,f435,f86])).

fof(f435,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f213,f378,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f378,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f213,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f212])).

fof(f296,plain,
    ( v3_ordinal1(sK6(sK0,sK0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f65,f218,f84])).

fof(f218,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f703,plain,
    ( r1_ordinal1(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f65,f296,f540,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f540,plain,
    ( ~ r1_ordinal1(sK0,sK6(sK0,sK0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f65,f296,f300,f86])).

fof(f300,plain,
    ( ~ r1_tarski(sK0,sK6(sK0,sK0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f218,f103])).

fof(f379,plain,
    ( spl8_6
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f374,f122,f376,f212])).

fof(f374,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f260])).

fof(f260,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f246,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f219,plain,
    ( spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f210,f122,f216,f212])).

fof(f210,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK6(sK0,X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f155,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f155,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f124,f81])).

fof(f143,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f105,f141,f122])).

fof(f105,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f66,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f139,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f67,f136,f122])).

fof(f67,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f134,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f68,f131,f122])).

fof(f68,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f104,f126,f122])).

fof(f104,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f69,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (30892)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.46  % (30916)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.46  % (30900)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (30914)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (30906)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (30914)Refutation not found, incomplete strategy% (30914)------------------------------
% 0.21/0.51  % (30914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30898)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (30914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30914)Memory used [KB]: 10746
% 0.21/0.51  % (30914)Time elapsed: 0.056 s
% 0.21/0.51  % (30914)------------------------------
% 0.21/0.51  % (30914)------------------------------
% 0.21/0.51  % (30896)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30893)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (30897)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (30894)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (30895)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (30912)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (30904)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (30899)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (30903)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (30894)Refutation not found, incomplete strategy% (30894)------------------------------
% 0.21/0.54  % (30894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30894)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30894)Memory used [KB]: 10746
% 0.21/0.54  % (30894)Time elapsed: 0.124 s
% 0.21/0.54  % (30894)------------------------------
% 0.21/0.54  % (30894)------------------------------
% 0.21/0.54  % (30918)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (30919)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (30910)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (30915)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (30902)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (30920)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (30917)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (30921)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (30908)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (30911)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (30909)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (30913)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (30912)Refutation not found, incomplete strategy% (30912)------------------------------
% 0.21/0.55  % (30912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30912)Memory used [KB]: 10746
% 0.21/0.55  % (30912)Time elapsed: 0.152 s
% 0.21/0.55  % (30912)------------------------------
% 0.21/0.55  % (30912)------------------------------
% 0.21/0.55  % (30913)Refutation not found, incomplete strategy% (30913)------------------------------
% 0.21/0.55  % (30913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30913)Memory used [KB]: 1663
% 0.21/0.55  % (30913)Time elapsed: 0.149 s
% 0.21/0.55  % (30913)------------------------------
% 0.21/0.55  % (30913)------------------------------
% 0.21/0.55  % (30907)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (30905)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (30901)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.14/0.64  % (30968)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.14/0.66  % (30981)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.14/0.69  % (30984)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.14/0.69  % (30918)Refutation found. Thanks to Tanya!
% 2.14/0.69  % SZS status Theorem for theBenchmark
% 2.14/0.69  % SZS output start Proof for theBenchmark
% 2.14/0.69  fof(f1850,plain,(
% 2.14/0.69    $false),
% 2.14/0.69    inference(avatar_sat_refutation,[],[f129,f134,f139,f143,f219,f379,f709,f764,f1849])).
% 2.14/0.69  fof(f1849,plain,(
% 2.14/0.69    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f1848])).
% 2.14/0.69  fof(f1848,plain,(
% 2.14/0.69    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.14/0.69    inference(subsumption_resolution,[],[f1847,f1328])).
% 2.14/0.69  fof(f1328,plain,(
% 2.14/0.69    r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.14/0.69    inference(forward_demodulation,[],[f1321,f948])).
% 2.14/0.69  fof(f948,plain,(
% 2.14/0.69    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f128,f808,f114])).
% 2.14/0.69  fof(f114,plain,(
% 2.14/0.69    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 2.14/0.69    inference(definition_unfolding,[],[f100,f71])).
% 2.14/0.69  fof(f71,plain,(
% 2.14/0.69    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.14/0.69    inference(cnf_transformation,[],[f5])).
% 2.14/0.69  fof(f5,axiom,(
% 2.14/0.69    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.14/0.69  fof(f100,plain,(
% 2.14/0.69    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.14/0.69    inference(cnf_transformation,[],[f64])).
% 2.14/0.69  fof(f64,plain,(
% 2.14/0.69    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.14/0.69    inference(flattening,[],[f63])).
% 2.14/0.69  fof(f63,plain,(
% 2.14/0.69    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.14/0.69    inference(nnf_transformation,[],[f9])).
% 2.14/0.69  fof(f9,axiom,(
% 2.14/0.69    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 2.14/0.69  fof(f808,plain,(
% 2.14/0.69    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),k2_xboole_0(sK0,k1_tarski(sK0))) | (~spl8_3 | ~spl8_4)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f225,f773,f110])).
% 2.14/0.69  fof(f110,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(definition_unfolding,[],[f76,f71])).
% 2.14/0.69  fof(f76,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f44])).
% 2.14/0.69  fof(f44,plain,(
% 2.14/0.69    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(nnf_transformation,[],[f24])).
% 2.14/0.69  fof(f24,plain,(
% 2.14/0.69    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(ennf_transformation,[],[f14])).
% 2.14/0.69  fof(f14,axiom,(
% 2.14/0.69    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 2.14/0.69  fof(f773,plain,(
% 2.14/0.69    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | (~spl8_3 | ~spl8_4)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f138,f65,f133,f109])).
% 2.14/0.69  fof(f109,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(definition_unfolding,[],[f73,f71])).
% 2.14/0.69  fof(f73,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f43])).
% 2.14/0.69  fof(f43,plain,(
% 2.14/0.69    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(nnf_transformation,[],[f23])).
% 2.14/0.69  fof(f23,plain,(
% 2.14/0.69    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(ennf_transformation,[],[f13])).
% 2.14/0.69  fof(f13,axiom,(
% 2.14/0.69    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 2.14/0.69  fof(f133,plain,(
% 2.14/0.69    r2_hidden(sK1,sK0) | ~spl8_3),
% 2.14/0.69    inference(avatar_component_clause,[],[f131])).
% 2.14/0.69  fof(f131,plain,(
% 2.14/0.69    spl8_3 <=> r2_hidden(sK1,sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.14/0.69  fof(f138,plain,(
% 2.14/0.69    v3_ordinal1(sK1) | ~spl8_4),
% 2.14/0.69    inference(avatar_component_clause,[],[f136])).
% 2.14/0.69  fof(f136,plain,(
% 2.14/0.69    spl8_4 <=> v3_ordinal1(sK1)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.14/0.69  fof(f225,plain,(
% 2.14/0.69    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f138,f107])).
% 2.14/0.69  fof(f107,plain,(
% 2.14/0.69    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(definition_unfolding,[],[f72,f71])).
% 2.14/0.69  fof(f72,plain,(
% 2.14/0.69    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f22])).
% 2.14/0.69  fof(f22,plain,(
% 2.14/0.69    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(ennf_transformation,[],[f12])).
% 2.14/0.69  fof(f12,axiom,(
% 2.14/0.69    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 2.14/0.69  fof(f65,plain,(
% 2.14/0.69    v3_ordinal1(sK0)),
% 2.14/0.69    inference(cnf_transformation,[],[f42])).
% 2.14/0.69  fof(f42,plain,(
% 2.14/0.69    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 2.14/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 2.14/0.69  fof(f40,plain,(
% 2.14/0.69    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 2.14/0.69    introduced(choice_axiom,[])).
% 2.14/0.69  fof(f41,plain,(
% 2.14/0.69    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 2.14/0.69    introduced(choice_axiom,[])).
% 2.14/0.69  fof(f39,plain,(
% 2.14/0.69    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.14/0.69    inference(rectify,[],[f38])).
% 2.14/0.69  fof(f38,plain,(
% 2.14/0.69    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.14/0.69    inference(flattening,[],[f37])).
% 2.14/0.69  fof(f37,plain,(
% 2.14/0.69    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.14/0.69    inference(nnf_transformation,[],[f21])).
% 2.14/0.69  fof(f21,plain,(
% 2.14/0.69    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.14/0.69    inference(flattening,[],[f20])).
% 2.14/0.69  fof(f20,plain,(
% 2.14/0.69    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.14/0.69    inference(ennf_transformation,[],[f19])).
% 2.14/0.69  fof(f19,negated_conjecture,(
% 2.14/0.69    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.14/0.69    inference(negated_conjecture,[],[f18])).
% 2.14/0.69  fof(f18,conjecture,(
% 2.14/0.69    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 2.14/0.69  fof(f128,plain,(
% 2.14/0.69    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 2.14/0.69    inference(avatar_component_clause,[],[f126])).
% 2.14/0.69  fof(f126,plain,(
% 2.14/0.69    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.14/0.69  fof(f1321,plain,(
% 2.14/0.69    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f138,f872,f1293,f109])).
% 2.14/0.69  fof(f1293,plain,(
% 2.14/0.69    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f869,f84])).
% 2.14/0.69  fof(f84,plain,(
% 2.14/0.69    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f30])).
% 2.14/0.69  fof(f30,plain,(
% 2.14/0.69    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.14/0.69    inference(flattening,[],[f29])).
% 2.14/0.69  fof(f29,plain,(
% 2.14/0.69    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.14/0.69    inference(ennf_transformation,[],[f10])).
% 2.14/0.69  fof(f10,axiom,(
% 2.14/0.69    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 2.14/0.69  fof(f869,plain,(
% 2.14/0.69    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f133,f798])).
% 2.14/0.69  fof(f798,plain,(
% 2.14/0.69    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 2.14/0.69    inference(superposition,[],[f118,f765])).
% 2.14/0.69  fof(f765,plain,(
% 2.14/0.69    sK0 = k3_tarski(sK0) | ~spl8_1),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f123,f80])).
% 2.14/0.69  fof(f80,plain,(
% 2.14/0.69    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f47])).
% 2.14/0.69  fof(f47,plain,(
% 2.14/0.69    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 2.14/0.69    inference(nnf_transformation,[],[f6])).
% 2.14/0.69  fof(f6,axiom,(
% 2.14/0.69    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 2.14/0.69  fof(f123,plain,(
% 2.14/0.69    v4_ordinal1(sK0) | ~spl8_1),
% 2.14/0.69    inference(avatar_component_clause,[],[f122])).
% 2.14/0.69  fof(f122,plain,(
% 2.14/0.69    spl8_1 <=> v4_ordinal1(sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.14/0.69  fof(f118,plain,(
% 2.14/0.69    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.14/0.69    inference(equality_resolution,[],[f95])).
% 2.14/0.69  fof(f95,plain,(
% 2.14/0.69    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.14/0.69    inference(cnf_transformation,[],[f62])).
% 2.14/0.69  fof(f62,plain,(
% 2.14/0.69    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.14/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f58,f61,f60,f59])).
% 2.14/0.69  fof(f59,plain,(
% 2.14/0.69    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 2.14/0.69    introduced(choice_axiom,[])).
% 2.14/0.69  fof(f60,plain,(
% 2.14/0.69    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 2.14/0.69    introduced(choice_axiom,[])).
% 2.14/0.69  fof(f61,plain,(
% 2.14/0.69    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 2.14/0.69    introduced(choice_axiom,[])).
% 2.14/0.69  fof(f58,plain,(
% 2.14/0.69    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.14/0.69    inference(rectify,[],[f57])).
% 2.14/0.69  fof(f57,plain,(
% 2.14/0.69    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.14/0.69    inference(nnf_transformation,[],[f3])).
% 2.14/0.69  fof(f3,axiom,(
% 2.14/0.69    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.14/0.69  fof(f872,plain,(
% 2.14/0.69    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f133,f799])).
% 2.14/0.69  fof(f799,plain,(
% 2.14/0.69    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 2.14/0.69    inference(superposition,[],[f119,f765])).
% 2.14/0.69  fof(f119,plain,(
% 2.14/0.69    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.14/0.69    inference(equality_resolution,[],[f94])).
% 2.14/0.69  fof(f94,plain,(
% 2.14/0.69    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.14/0.69    inference(cnf_transformation,[],[f62])).
% 2.14/0.69  fof(f1847,plain,(
% 2.14/0.69    ~r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f1293,f1297,f86])).
% 2.14/0.69  fof(f86,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f50])).
% 2.14/0.69  fof(f50,plain,(
% 2.14/0.69    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(nnf_transformation,[],[f34])).
% 2.14/0.69  fof(f34,plain,(
% 2.14/0.69    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(flattening,[],[f33])).
% 2.14/0.69  fof(f33,plain,(
% 2.14/0.69    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.14/0.69    inference(ennf_transformation,[],[f7])).
% 2.14/0.69  fof(f7,axiom,(
% 2.14/0.69    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 2.14/0.69  fof(f1297,plain,(
% 2.14/0.69    ~r1_tarski(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f869,f103])).
% 2.14/0.69  fof(f103,plain,(
% 2.14/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f36])).
% 2.14/0.69  fof(f36,plain,(
% 2.14/0.69    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.14/0.69    inference(ennf_transformation,[],[f17])).
% 2.14/0.69  fof(f17,axiom,(
% 2.14/0.69    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.14/0.69  fof(f764,plain,(
% 2.14/0.69    spl8_1 | ~spl8_5 | ~spl8_6),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f763])).
% 2.14/0.69  fof(f763,plain,(
% 2.14/0.69    $false | (spl8_1 | ~spl8_5 | ~spl8_6)),
% 2.14/0.69    inference(subsumption_resolution,[],[f762,f716])).
% 2.14/0.69  fof(f716,plain,(
% 2.14/0.69    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_6)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f246,f106,f214,f99])).
% 2.14/0.69  fof(f99,plain,(
% 2.14/0.69    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f62])).
% 2.14/0.69  fof(f214,plain,(
% 2.14/0.69    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_6),
% 2.14/0.69    inference(avatar_component_clause,[],[f212])).
% 2.14/0.69  fof(f212,plain,(
% 2.14/0.69    spl8_6 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.14/0.69  fof(f106,plain,(
% 2.14/0.69    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.14/0.69    inference(definition_unfolding,[],[f70,f71])).
% 2.14/0.69  fof(f70,plain,(
% 2.14/0.69    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.14/0.69    inference(cnf_transformation,[],[f8])).
% 2.14/0.69  fof(f8,axiom,(
% 2.14/0.69    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.14/0.69  fof(f246,plain,(
% 2.14/0.69    sK0 != k3_tarski(sK0) | spl8_1),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f124,f81])).
% 2.14/0.69  fof(f81,plain,(
% 2.14/0.69    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 2.14/0.69    inference(cnf_transformation,[],[f47])).
% 2.14/0.69  fof(f124,plain,(
% 2.14/0.69    ~v4_ordinal1(sK0) | spl8_1),
% 2.14/0.69    inference(avatar_component_clause,[],[f122])).
% 2.14/0.69  fof(f762,plain,(
% 2.14/0.69    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_6)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f214,f717,f142])).
% 2.14/0.69  fof(f142,plain,(
% 2.14/0.69    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 2.14/0.69    inference(avatar_component_clause,[],[f141])).
% 2.14/0.69  fof(f141,plain,(
% 2.14/0.69    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.14/0.69  fof(f717,plain,(
% 2.14/0.69    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_6),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f214,f84])).
% 2.14/0.69  fof(f709,plain,(
% 2.14/0.69    spl8_6 | ~spl8_7 | ~spl8_8),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f708])).
% 2.14/0.69  fof(f708,plain,(
% 2.14/0.69    $false | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 2.14/0.69    inference(subsumption_resolution,[],[f703,f578])).
% 2.14/0.69  fof(f578,plain,(
% 2.14/0.69    ~r1_ordinal1(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f296,f435,f86])).
% 2.14/0.69  fof(f435,plain,(
% 2.14/0.69    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_8)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f213,f378,f91])).
% 2.14/0.69  fof(f91,plain,(
% 2.14/0.69    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f56])).
% 2.14/0.69  fof(f56,plain,(
% 2.14/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 2.14/0.69  fof(f55,plain,(
% 2.14/0.69    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.14/0.69    introduced(choice_axiom,[])).
% 2.14/0.69  fof(f54,plain,(
% 2.14/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.69    inference(rectify,[],[f53])).
% 2.14/0.69  fof(f53,plain,(
% 2.14/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.69    inference(nnf_transformation,[],[f35])).
% 2.14/0.69  fof(f35,plain,(
% 2.14/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.14/0.69    inference(ennf_transformation,[],[f1])).
% 2.14/0.69  fof(f1,axiom,(
% 2.14/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.14/0.69  fof(f378,plain,(
% 2.14/0.69    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_8),
% 2.14/0.69    inference(avatar_component_clause,[],[f376])).
% 2.14/0.69  fof(f376,plain,(
% 2.14/0.69    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.14/0.69  fof(f213,plain,(
% 2.14/0.69    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_6),
% 2.14/0.69    inference(avatar_component_clause,[],[f212])).
% 2.14/0.69  fof(f296,plain,(
% 2.14/0.69    v3_ordinal1(sK6(sK0,sK0)) | ~spl8_7),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f218,f84])).
% 2.14/0.69  fof(f218,plain,(
% 2.14/0.69    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_7),
% 2.14/0.69    inference(avatar_component_clause,[],[f216])).
% 2.14/0.69  fof(f216,plain,(
% 2.14/0.69    spl8_7 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.14/0.69  fof(f703,plain,(
% 2.14/0.69    r1_ordinal1(sK6(sK0,sK0),sK0) | ~spl8_7),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f296,f540,f85])).
% 2.14/0.69  fof(f85,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f32])).
% 2.14/0.69  fof(f32,plain,(
% 2.14/0.69    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.14/0.69    inference(flattening,[],[f31])).
% 2.14/0.69  fof(f31,plain,(
% 2.14/0.69    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.14/0.69    inference(ennf_transformation,[],[f4])).
% 2.14/0.69  fof(f4,axiom,(
% 2.14/0.69    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 2.14/0.69  fof(f540,plain,(
% 2.14/0.69    ~r1_ordinal1(sK0,sK6(sK0,sK0)) | ~spl8_7),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f65,f296,f300,f86])).
% 2.14/0.69  fof(f300,plain,(
% 2.14/0.69    ~r1_tarski(sK0,sK6(sK0,sK0)) | ~spl8_7),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f218,f103])).
% 2.14/0.69  fof(f379,plain,(
% 2.14/0.69    spl8_6 | spl8_8 | spl8_1),
% 2.14/0.69    inference(avatar_split_clause,[],[f374,f122,f376,f212])).
% 2.14/0.69  fof(f374,plain,(
% 2.14/0.69    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 2.14/0.69    inference(equality_resolution,[],[f260])).
% 2.14/0.69  fof(f260,plain,(
% 2.14/0.69    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 2.14/0.69    inference(superposition,[],[f246,f97])).
% 2.14/0.69  fof(f97,plain,(
% 2.14/0.69    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f62])).
% 2.14/0.69  fof(f219,plain,(
% 2.14/0.69    spl8_6 | spl8_7 | spl8_1),
% 2.14/0.69    inference(avatar_split_clause,[],[f210,f122,f216,f212])).
% 2.14/0.69  fof(f210,plain,(
% 2.14/0.69    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 2.14/0.69    inference(equality_resolution,[],[f160])).
% 2.14/0.69  fof(f160,plain,(
% 2.14/0.69    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 2.14/0.69    inference(superposition,[],[f155,f98])).
% 2.14/0.69  fof(f98,plain,(
% 2.14/0.69    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f62])).
% 2.14/0.69  fof(f155,plain,(
% 2.14/0.69    sK0 != k3_tarski(sK0) | spl8_1),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f124,f81])).
% 2.14/0.69  fof(f143,plain,(
% 2.14/0.69    spl8_1 | spl8_5),
% 2.14/0.69    inference(avatar_split_clause,[],[f105,f141,f122])).
% 2.14/0.69  fof(f105,plain,(
% 2.14/0.69    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.14/0.69    inference(definition_unfolding,[],[f66,f71])).
% 2.14/0.69  fof(f66,plain,(
% 2.14/0.69    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f42])).
% 2.14/0.69  fof(f139,plain,(
% 2.14/0.69    ~spl8_1 | spl8_4),
% 2.14/0.69    inference(avatar_split_clause,[],[f67,f136,f122])).
% 2.14/0.69  fof(f67,plain,(
% 2.14/0.69    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.14/0.69    inference(cnf_transformation,[],[f42])).
% 2.14/0.69  fof(f134,plain,(
% 2.14/0.69    ~spl8_1 | spl8_3),
% 2.14/0.69    inference(avatar_split_clause,[],[f68,f131,f122])).
% 2.14/0.69  fof(f68,plain,(
% 2.14/0.69    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 2.14/0.69    inference(cnf_transformation,[],[f42])).
% 2.14/0.69  fof(f129,plain,(
% 2.14/0.69    ~spl8_1 | ~spl8_2),
% 2.14/0.69    inference(avatar_split_clause,[],[f104,f126,f122])).
% 2.14/0.69  fof(f104,plain,(
% 2.14/0.69    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 2.14/0.69    inference(definition_unfolding,[],[f69,f71])).
% 2.14/0.69  fof(f69,plain,(
% 2.14/0.69    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 2.14/0.69    inference(cnf_transformation,[],[f42])).
% 2.14/0.69  % SZS output end Proof for theBenchmark
% 2.14/0.69  % (30918)------------------------------
% 2.14/0.69  % (30918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.69  % (30918)Termination reason: Refutation
% 2.14/0.69  
% 2.14/0.69  % (30918)Memory used [KB]: 11897
% 2.14/0.69  % (30918)Time elapsed: 0.293 s
% 2.14/0.69  % (30918)------------------------------
% 2.14/0.69  % (30918)------------------------------
% 2.14/0.70  % (30891)Success in time 0.327 s
%------------------------------------------------------------------------------
