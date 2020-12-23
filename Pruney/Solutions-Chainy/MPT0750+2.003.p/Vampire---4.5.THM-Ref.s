%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:40 EST 2020

% Result     : Theorem 3.49s
% Output     : Refutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 393 expanded)
%              Number of leaves         :   28 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :  497 (1956 expanded)
%              Number of equality atoms :   29 ( 110 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f137,f142,f146,f220,f373,f485,f569,f2255])).

fof(f2255,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f2254])).

fof(f2254,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f2253,f682])).

fof(f682,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f136,f601])).

fof(f601,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f121,f570])).

fof(f570,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f126,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f126,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f121,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f62,f65,f64,f63])).

fof(f63,plain,(
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

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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

fof(f136,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f2253,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f2252,f908])).

fof(f908,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f69,f227,f131,f643,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f643,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f69,f141,f588,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f78,f75])).

fof(f75,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f588,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f69,f141,f580,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f580,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f136,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f141,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f131,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f227,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f141,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f76,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f69,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).

fof(f45,plain,
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

fof(f46,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f2252,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f141,f875,f1883,f114])).

fof(f1883,plain,
    ( ~ r1_ordinal1(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f141,f875,f888,f91])).

fof(f888,plain,
    ( ~ r1_tarski(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f695,f108])).

fof(f695,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f136,f602])).

fof(f602,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f122,f570])).

fof(f122,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f875,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f69,f682,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f569,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f567,f491])).

fof(f491,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f247,f111,f215,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f215,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f111,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f247,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f127,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f127,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f567,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f215,f494,f145])).

fof(f145,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f494,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f69,f215,f89])).

fof(f485,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f477,f379])).

fof(f379,plain,
    ( r1_tarski(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f147,f219,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f219,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f147,plain,(
    v1_ordinal1(sK0) ),
    inference(unit_resulting_resolution,[],[f69,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f477,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f214,f372,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f372,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f214,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f373,plain,
    ( spl8_6
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f368,f125,f370,f213])).

fof(f368,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f261])).

fof(f261,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f247,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f220,plain,
    ( spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f211,f125,f217,f213])).

fof(f211,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f163])).

fof(f163,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK6(sK0,X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f158,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f158,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f127,f84])).

fof(f146,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f110,f144,f125])).

fof(f110,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f70,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f142,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f71,f139,f125])).

fof(f71,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f72,f134,f125])).

fof(f72,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f109,f129,f125])).

fof(f109,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f73,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:05:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (4861)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (4840)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (4845)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (4853)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (4850)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (4838)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (4864)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (4841)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (4856)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (4859)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (4839)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (4851)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.58  % (4856)Refutation not found, incomplete strategy% (4856)------------------------------
% 0.22/0.58  % (4856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (4856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (4856)Memory used [KB]: 10746
% 0.22/0.58  % (4856)Time elapsed: 0.151 s
% 0.22/0.58  % (4856)------------------------------
% 0.22/0.58  % (4856)------------------------------
% 0.22/0.59  % (4836)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (4837)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (4842)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.60  % (4843)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.60  % (4865)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (4846)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  % (4858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.61  % (4847)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.61  % (4857)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.61  % (4857)Refutation not found, incomplete strategy% (4857)------------------------------
% 0.22/0.61  % (4857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (4857)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (4857)Memory used [KB]: 1663
% 0.22/0.61  % (4857)Time elapsed: 0.182 s
% 0.22/0.61  % (4857)------------------------------
% 0.22/0.61  % (4857)------------------------------
% 0.22/0.61  % (4854)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.61  % (4848)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.61  % (4849)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.62  % (4844)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.62  % (4860)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.62  % (4855)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.62  % (4852)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.62  % (4863)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.63  % (4862)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.63  % (4858)Refutation not found, incomplete strategy% (4858)------------------------------
% 0.22/0.63  % (4858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.63  % (4858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.63  
% 0.22/0.63  % (4858)Memory used [KB]: 10746
% 0.22/0.63  % (4858)Time elapsed: 0.184 s
% 0.22/0.63  % (4858)------------------------------
% 0.22/0.63  % (4858)------------------------------
% 2.61/0.72  % (4890)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.77/0.76  % (4891)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.77/0.77  % (4892)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.49/0.84  % (4862)Refutation found. Thanks to Tanya!
% 3.49/0.84  % SZS status Theorem for theBenchmark
% 3.49/0.84  % SZS output start Proof for theBenchmark
% 3.49/0.84  fof(f2256,plain,(
% 3.49/0.84    $false),
% 3.49/0.84    inference(avatar_sat_refutation,[],[f132,f137,f142,f146,f220,f373,f485,f569,f2255])).
% 3.49/0.84  fof(f2255,plain,(
% 3.49/0.84    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 3.49/0.84    inference(avatar_contradiction_clause,[],[f2254])).
% 3.49/0.84  fof(f2254,plain,(
% 3.49/0.84    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(subsumption_resolution,[],[f2253,f682])).
% 3.49/0.84  fof(f682,plain,(
% 3.49/0.84    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f136,f601])).
% 3.49/0.84  fof(f601,plain,(
% 3.49/0.84    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 3.49/0.84    inference(superposition,[],[f121,f570])).
% 3.49/0.84  fof(f570,plain,(
% 3.49/0.84    sK0 = k3_tarski(sK0) | ~spl8_1),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f126,f83])).
% 3.49/0.84  fof(f83,plain,(
% 3.49/0.84    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f51])).
% 3.49/0.84  fof(f51,plain,(
% 3.49/0.84    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 3.49/0.84    inference(nnf_transformation,[],[f8])).
% 3.49/0.84  fof(f8,axiom,(
% 3.49/0.84    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 3.49/0.84  fof(f126,plain,(
% 3.49/0.84    v4_ordinal1(sK0) | ~spl8_1),
% 3.49/0.84    inference(avatar_component_clause,[],[f125])).
% 3.49/0.84  fof(f125,plain,(
% 3.49/0.84    spl8_1 <=> v4_ordinal1(sK0)),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.49/0.84  fof(f121,plain,(
% 3.49/0.84    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.49/0.84    inference(equality_resolution,[],[f100])).
% 3.49/0.84  fof(f100,plain,(
% 3.49/0.84    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.49/0.84    inference(cnf_transformation,[],[f66])).
% 3.49/0.84  fof(f66,plain,(
% 3.49/0.84    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.49/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f62,f65,f64,f63])).
% 3.49/0.84  fof(f63,plain,(
% 3.49/0.84    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 3.49/0.84    introduced(choice_axiom,[])).
% 3.49/0.84  fof(f64,plain,(
% 3.49/0.84    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 3.49/0.84    introduced(choice_axiom,[])).
% 3.49/0.84  fof(f65,plain,(
% 3.49/0.84    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 3.49/0.84    introduced(choice_axiom,[])).
% 3.49/0.84  fof(f62,plain,(
% 3.49/0.84    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.49/0.84    inference(rectify,[],[f61])).
% 3.49/0.84  fof(f61,plain,(
% 3.49/0.84    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.49/0.84    inference(nnf_transformation,[],[f3])).
% 3.49/0.84  fof(f3,axiom,(
% 3.49/0.84    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 3.49/0.84  fof(f136,plain,(
% 3.49/0.84    r2_hidden(sK1,sK0) | ~spl8_3),
% 3.49/0.84    inference(avatar_component_clause,[],[f134])).
% 3.49/0.84  fof(f134,plain,(
% 3.49/0.84    spl8_3 <=> r2_hidden(sK1,sK0)),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.49/0.84  fof(f2253,plain,(
% 3.49/0.84    ~r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(forward_demodulation,[],[f2252,f908])).
% 3.49/0.84  fof(f908,plain,(
% 3.49/0.84    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f69,f227,f131,f643,f80])).
% 3.49/0.84  fof(f80,plain,(
% 3.49/0.84    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f29])).
% 3.49/0.84  fof(f29,plain,(
% 3.49/0.84    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(flattening,[],[f28])).
% 3.49/0.84  fof(f28,plain,(
% 3.49/0.84    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(ennf_transformation,[],[f13])).
% 3.49/0.84  fof(f13,axiom,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 3.49/0.84  fof(f643,plain,(
% 3.49/0.84    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f69,f141,f588,f114])).
% 3.49/0.84  fof(f114,plain,(
% 3.49/0.84    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(definition_unfolding,[],[f78,f75])).
% 3.49/0.84  fof(f75,plain,(
% 3.49/0.84    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.49/0.84    inference(cnf_transformation,[],[f6])).
% 3.49/0.84  fof(f6,axiom,(
% 3.49/0.84    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 3.49/0.84  fof(f78,plain,(
% 3.49/0.84    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f48])).
% 3.49/0.84  fof(f48,plain,(
% 3.49/0.84    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(nnf_transformation,[],[f27])).
% 3.49/0.84  fof(f27,plain,(
% 3.49/0.84    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(ennf_transformation,[],[f15])).
% 3.49/0.84  fof(f15,axiom,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 3.49/0.84  fof(f588,plain,(
% 3.49/0.84    ~r1_ordinal1(sK0,sK1) | (~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f69,f141,f580,f91])).
% 3.49/0.84  fof(f91,plain,(
% 3.49/0.84    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f54])).
% 3.49/0.84  fof(f54,plain,(
% 3.49/0.84    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(nnf_transformation,[],[f39])).
% 3.49/0.84  fof(f39,plain,(
% 3.49/0.84    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(flattening,[],[f38])).
% 3.49/0.84  fof(f38,plain,(
% 3.49/0.84    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.49/0.84    inference(ennf_transformation,[],[f9])).
% 3.49/0.84  fof(f9,axiom,(
% 3.49/0.84    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 3.49/0.84  fof(f580,plain,(
% 3.49/0.84    ~r1_tarski(sK0,sK1) | ~spl8_3),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f136,f108])).
% 3.49/0.84  fof(f108,plain,(
% 3.49/0.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f41])).
% 3.49/0.84  fof(f41,plain,(
% 3.49/0.84    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.49/0.84    inference(ennf_transformation,[],[f18])).
% 3.49/0.84  fof(f18,axiom,(
% 3.49/0.84    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.49/0.84  fof(f141,plain,(
% 3.49/0.84    v3_ordinal1(sK1) | ~spl8_4),
% 3.49/0.84    inference(avatar_component_clause,[],[f139])).
% 3.49/0.84  fof(f139,plain,(
% 3.49/0.84    spl8_4 <=> v3_ordinal1(sK1)),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.49/0.84  fof(f131,plain,(
% 3.49/0.84    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 3.49/0.84    inference(avatar_component_clause,[],[f129])).
% 3.49/0.84  fof(f129,plain,(
% 3.49/0.84    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.49/0.84  fof(f227,plain,(
% 3.49/0.84    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f141,f112])).
% 3.49/0.84  fof(f112,plain,(
% 3.49/0.84    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(definition_unfolding,[],[f76,f75])).
% 3.49/0.84  fof(f76,plain,(
% 3.49/0.84    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f25])).
% 3.49/0.84  fof(f25,plain,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(ennf_transformation,[],[f14])).
% 3.49/0.84  fof(f14,axiom,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 3.49/0.84  fof(f69,plain,(
% 3.49/0.84    v3_ordinal1(sK0)),
% 3.49/0.84    inference(cnf_transformation,[],[f47])).
% 3.49/0.84  fof(f47,plain,(
% 3.49/0.84    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 3.49/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 3.49/0.84  fof(f45,plain,(
% 3.49/0.84    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 3.49/0.84    introduced(choice_axiom,[])).
% 3.49/0.84  fof(f46,plain,(
% 3.49/0.84    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 3.49/0.84    introduced(choice_axiom,[])).
% 3.49/0.84  fof(f44,plain,(
% 3.49/0.84    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.49/0.84    inference(rectify,[],[f43])).
% 3.49/0.84  fof(f43,plain,(
% 3.49/0.84    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.49/0.84    inference(flattening,[],[f42])).
% 3.49/0.84  fof(f42,plain,(
% 3.49/0.84    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.49/0.84    inference(nnf_transformation,[],[f24])).
% 3.49/0.84  fof(f24,plain,(
% 3.49/0.84    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.49/0.84    inference(flattening,[],[f23])).
% 3.49/0.84  fof(f23,plain,(
% 3.49/0.84    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.49/0.84    inference(ennf_transformation,[],[f20])).
% 3.49/0.84  fof(f20,negated_conjecture,(
% 3.49/0.84    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.49/0.84    inference(negated_conjecture,[],[f19])).
% 3.49/0.84  fof(f19,conjecture,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 3.49/0.84  fof(f2252,plain,(
% 3.49/0.84    ~r2_hidden(sK7(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f141,f875,f1883,f114])).
% 3.49/0.84  fof(f1883,plain,(
% 3.49/0.84    ~r1_ordinal1(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f141,f875,f888,f91])).
% 3.49/0.84  fof(f888,plain,(
% 3.49/0.84    ~r1_tarski(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f695,f108])).
% 3.49/0.84  fof(f695,plain,(
% 3.49/0.84    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f136,f602])).
% 3.49/0.84  fof(f602,plain,(
% 3.49/0.84    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 3.49/0.84    inference(superposition,[],[f122,f570])).
% 3.49/0.84  fof(f122,plain,(
% 3.49/0.84    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.49/0.84    inference(equality_resolution,[],[f99])).
% 3.49/0.84  fof(f99,plain,(
% 3.49/0.84    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.49/0.84    inference(cnf_transformation,[],[f66])).
% 3.49/0.84  fof(f875,plain,(
% 3.49/0.84    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f69,f682,f89])).
% 3.49/0.84  fof(f89,plain,(
% 3.49/0.84    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f35])).
% 3.49/0.84  fof(f35,plain,(
% 3.49/0.84    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.49/0.84    inference(flattening,[],[f34])).
% 3.49/0.84  fof(f34,plain,(
% 3.49/0.84    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.49/0.84    inference(ennf_transformation,[],[f12])).
% 3.49/0.84  fof(f12,axiom,(
% 3.49/0.84    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 3.49/0.84  fof(f569,plain,(
% 3.49/0.84    spl8_1 | ~spl8_5 | ~spl8_6),
% 3.49/0.84    inference(avatar_contradiction_clause,[],[f568])).
% 3.49/0.84  fof(f568,plain,(
% 3.49/0.84    $false | (spl8_1 | ~spl8_5 | ~spl8_6)),
% 3.49/0.84    inference(subsumption_resolution,[],[f567,f491])).
% 3.49/0.84  fof(f491,plain,(
% 3.49/0.84    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_6)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f247,f111,f215,f104])).
% 3.49/0.84  fof(f104,plain,(
% 3.49/0.84    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f66])).
% 3.49/0.84  fof(f215,plain,(
% 3.49/0.84    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_6),
% 3.49/0.84    inference(avatar_component_clause,[],[f213])).
% 3.49/0.84  fof(f213,plain,(
% 3.49/0.84    spl8_6 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.49/0.84  fof(f111,plain,(
% 3.49/0.84    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 3.49/0.84    inference(definition_unfolding,[],[f74,f75])).
% 3.49/0.84  fof(f74,plain,(
% 3.49/0.84    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.49/0.84    inference(cnf_transformation,[],[f10])).
% 3.49/0.84  fof(f10,axiom,(
% 3.49/0.84    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 3.49/0.84  fof(f247,plain,(
% 3.49/0.84    sK0 != k3_tarski(sK0) | spl8_1),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f127,f84])).
% 3.49/0.84  fof(f84,plain,(
% 3.49/0.84    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 3.49/0.84    inference(cnf_transformation,[],[f51])).
% 3.49/0.84  fof(f127,plain,(
% 3.49/0.84    ~v4_ordinal1(sK0) | spl8_1),
% 3.49/0.84    inference(avatar_component_clause,[],[f125])).
% 3.49/0.84  fof(f567,plain,(
% 3.49/0.84    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_6)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f215,f494,f145])).
% 3.49/0.84  fof(f145,plain,(
% 3.49/0.84    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 3.49/0.84    inference(avatar_component_clause,[],[f144])).
% 3.49/0.84  fof(f144,plain,(
% 3.49/0.84    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.49/0.84  fof(f494,plain,(
% 3.49/0.84    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_6),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f69,f215,f89])).
% 3.49/0.84  fof(f485,plain,(
% 3.49/0.84    spl8_6 | ~spl8_7 | ~spl8_8),
% 3.49/0.84    inference(avatar_contradiction_clause,[],[f484])).
% 3.49/0.84  fof(f484,plain,(
% 3.49/0.84    $false | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 3.49/0.84    inference(subsumption_resolution,[],[f477,f379])).
% 3.49/0.84  fof(f379,plain,(
% 3.49/0.84    r1_tarski(sK6(sK0,sK0),sK0) | ~spl8_7),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f147,f219,f85])).
% 3.49/0.84  fof(f85,plain,(
% 3.49/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f31])).
% 3.49/0.84  fof(f31,plain,(
% 3.49/0.84    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 3.49/0.84    inference(ennf_transformation,[],[f21])).
% 3.49/0.84  fof(f21,plain,(
% 3.49/0.84    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.49/0.84    inference(unused_predicate_definition_removal,[],[f7])).
% 3.49/0.84  fof(f7,axiom,(
% 3.49/0.84    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 3.49/0.84  fof(f219,plain,(
% 3.49/0.84    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_7),
% 3.49/0.84    inference(avatar_component_clause,[],[f217])).
% 3.49/0.84  fof(f217,plain,(
% 3.49/0.84    spl8_7 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.49/0.84  fof(f147,plain,(
% 3.49/0.84    v1_ordinal1(sK0)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f69,f77])).
% 3.49/0.84  fof(f77,plain,(
% 3.49/0.84    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f26])).
% 3.49/0.84  fof(f26,plain,(
% 3.49/0.84    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.49/0.84    inference(ennf_transformation,[],[f22])).
% 3.49/0.84  fof(f22,plain,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.49/0.84    inference(pure_predicate_removal,[],[f4])).
% 3.49/0.84  fof(f4,axiom,(
% 3.49/0.84    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 3.49/0.84  fof(f477,plain,(
% 3.49/0.84    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_8)),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f214,f372,f96])).
% 3.49/0.84  fof(f96,plain,(
% 3.49/0.84    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f60])).
% 3.49/0.84  fof(f60,plain,(
% 3.49/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).
% 3.49/0.84  fof(f59,plain,(
% 3.49/0.84    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.49/0.84    introduced(choice_axiom,[])).
% 3.49/0.84  fof(f58,plain,(
% 3.49/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/0.84    inference(rectify,[],[f57])).
% 3.49/0.84  fof(f57,plain,(
% 3.49/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/0.84    inference(nnf_transformation,[],[f40])).
% 3.49/0.84  fof(f40,plain,(
% 3.49/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.49/0.84    inference(ennf_transformation,[],[f1])).
% 3.49/0.84  fof(f1,axiom,(
% 3.49/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.49/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.49/0.84  fof(f372,plain,(
% 3.49/0.84    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_8),
% 3.49/0.84    inference(avatar_component_clause,[],[f370])).
% 3.49/0.84  fof(f370,plain,(
% 3.49/0.84    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 3.49/0.84    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.49/0.84  fof(f214,plain,(
% 3.49/0.84    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_6),
% 3.49/0.84    inference(avatar_component_clause,[],[f213])).
% 3.49/0.84  fof(f373,plain,(
% 3.49/0.84    spl8_6 | spl8_8 | spl8_1),
% 3.49/0.84    inference(avatar_split_clause,[],[f368,f125,f370,f213])).
% 3.49/0.84  fof(f368,plain,(
% 3.49/0.84    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 3.49/0.84    inference(equality_resolution,[],[f261])).
% 3.49/0.84  fof(f261,plain,(
% 3.49/0.84    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 3.49/0.84    inference(superposition,[],[f247,f102])).
% 3.49/0.84  fof(f102,plain,(
% 3.49/0.84    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f66])).
% 3.49/0.84  fof(f220,plain,(
% 3.49/0.84    spl8_6 | spl8_7 | spl8_1),
% 3.49/0.84    inference(avatar_split_clause,[],[f211,f125,f217,f213])).
% 3.49/0.84  fof(f211,plain,(
% 3.49/0.84    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 3.49/0.84    inference(equality_resolution,[],[f163])).
% 3.49/0.84  fof(f163,plain,(
% 3.49/0.84    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 3.49/0.84    inference(superposition,[],[f158,f103])).
% 3.49/0.84  fof(f103,plain,(
% 3.49/0.84    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f66])).
% 3.49/0.84  fof(f158,plain,(
% 3.49/0.84    sK0 != k3_tarski(sK0) | spl8_1),
% 3.49/0.84    inference(unit_resulting_resolution,[],[f127,f84])).
% 3.49/0.84  fof(f146,plain,(
% 3.49/0.84    spl8_1 | spl8_5),
% 3.49/0.84    inference(avatar_split_clause,[],[f110,f144,f125])).
% 3.49/0.84  fof(f110,plain,(
% 3.49/0.84    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.49/0.84    inference(definition_unfolding,[],[f70,f75])).
% 3.49/0.84  fof(f70,plain,(
% 3.49/0.84    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.49/0.84    inference(cnf_transformation,[],[f47])).
% 3.49/0.84  fof(f142,plain,(
% 3.49/0.84    ~spl8_1 | spl8_4),
% 3.49/0.84    inference(avatar_split_clause,[],[f71,f139,f125])).
% 3.49/0.84  fof(f71,plain,(
% 3.49/0.84    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 3.49/0.84    inference(cnf_transformation,[],[f47])).
% 3.49/0.84  fof(f137,plain,(
% 3.49/0.84    ~spl8_1 | spl8_3),
% 3.49/0.84    inference(avatar_split_clause,[],[f72,f134,f125])).
% 3.49/0.84  fof(f72,plain,(
% 3.49/0.84    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 3.49/0.84    inference(cnf_transformation,[],[f47])).
% 3.49/0.84  fof(f132,plain,(
% 3.49/0.84    ~spl8_1 | ~spl8_2),
% 3.49/0.84    inference(avatar_split_clause,[],[f109,f129,f125])).
% 3.49/0.84  fof(f109,plain,(
% 3.49/0.84    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 3.49/0.84    inference(definition_unfolding,[],[f73,f75])).
% 3.49/0.84  fof(f73,plain,(
% 3.49/0.84    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 3.49/0.84    inference(cnf_transformation,[],[f47])).
% 3.49/0.84  % SZS output end Proof for theBenchmark
% 3.49/0.84  % (4862)------------------------------
% 3.49/0.84  % (4862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.84  % (4862)Termination reason: Refutation
% 3.49/0.84  
% 3.49/0.84  % (4862)Memory used [KB]: 12153
% 3.49/0.84  % (4862)Time elapsed: 0.411 s
% 3.49/0.84  % (4862)------------------------------
% 3.49/0.84  % (4862)------------------------------
% 3.49/0.84  % (4835)Success in time 0.478 s
%------------------------------------------------------------------------------
