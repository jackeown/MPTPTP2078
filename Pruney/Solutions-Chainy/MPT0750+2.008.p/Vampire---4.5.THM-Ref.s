%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:40 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 452 expanded)
%              Number of leaves         :   27 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  502 (2286 expanded)
%              Number of equality atoms :   34 ( 119 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f209,f354,f774,f825,f2588])).

fof(f2588,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f2587])).

fof(f2587,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f2586,f928])).

fof(f928,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f131,f854])).

fof(f854,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f116,f826])).

fof(f826,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f121,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f121,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f116,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f60,f59,f58])).

fof(f58,plain,(
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

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f131,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f2586,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f2585,f1146])).

fof(f1146,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f215,f126,f887,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f887,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f136,f842,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f73,f71])).

fof(f71,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f842,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f136,f833,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f833,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f131,f102])).

fof(f102,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f136,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f126,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f215,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f136,f107])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f2585,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f136,f1115,f2093,f109])).

fof(f2093,plain,
    ( ~ r1_ordinal1(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f136,f1115,f1128,f85])).

fof(f1128,plain,
    ( ~ r1_tarski(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f931,f102])).

fof(f931,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f131,f855])).

fof(f855,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f117,f826])).

fof(f117,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1115,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f64,f928,f83])).

fof(f83,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f825,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f823,f779])).

fof(f779,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f234,f106,f204,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f204,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f234,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f122,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f823,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f204,f782,f140])).

fof(f140,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f782,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f64,f204,f83])).

fof(f774,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f773])).

fof(f773,plain,
    ( $false
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f763,f640])).

fof(f640,plain,
    ( ~ r1_ordinal1(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f64,f335,f425,f85])).

fof(f425,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f203,f353,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f353,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f203,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f202])).

fof(f335,plain,
    ( v3_ordinal1(sK6(sK0,sK0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f64,f208,f83])).

fof(f208,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f763,plain,
    ( r1_ordinal1(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f64,f335,f340,f109])).

fof(f340,plain,
    ( r2_hidden(sK6(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f208,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f100,f71])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f354,plain,
    ( spl8_6
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f349,f120,f351,f202])).

fof(f349,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f248])).

fof(f248,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f234,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f209,plain,
    ( spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f200,f120,f206,f202])).

fof(f200,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK6(sK0,X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f152,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f152,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f122,f79])).

fof(f141,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f104,f139,f120])).

fof(f104,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f65,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f137,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f66,f134,f120])).

fof(f66,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f132,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f67,f129,f120])).

fof(f67,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f127,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f103,f124,f120])).

fof(f103,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f68,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:29:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (15347)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (15343)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15343)Refutation not found, incomplete strategy% (15343)------------------------------
% 0.22/0.54  % (15343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15368)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (15342)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (15344)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (15357)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (15360)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (15366)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (15345)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15341)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (15346)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (15343)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15343)Memory used [KB]: 10746
% 0.22/0.54  % (15343)Time elapsed: 0.125 s
% 0.22/0.54  % (15343)------------------------------
% 0.22/0.54  % (15343)------------------------------
% 0.22/0.55  % (15364)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (15354)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (15348)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (15373)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (15351)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (15349)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (15365)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (15372)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (15358)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (15365)Refutation not found, incomplete strategy% (15365)------------------------------
% 0.22/0.55  % (15365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15369)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (15359)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (15355)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (15350)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (15363)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (15362)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (15363)Refutation not found, incomplete strategy% (15363)------------------------------
% 0.22/0.56  % (15363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15363)Memory used [KB]: 10746
% 0.22/0.56  % (15363)Time elapsed: 0.144 s
% 0.22/0.56  % (15363)------------------------------
% 0.22/0.56  % (15363)------------------------------
% 0.22/0.57  % (15353)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (15364)Refutation not found, incomplete strategy% (15364)------------------------------
% 0.22/0.57  % (15364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (15356)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (15364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (15364)Memory used [KB]: 1663
% 0.22/0.57  % (15364)Time elapsed: 0.153 s
% 0.22/0.57  % (15364)------------------------------
% 0.22/0.57  % (15364)------------------------------
% 0.22/0.57  % (15367)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (15370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (15365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (15365)Memory used [KB]: 10746
% 0.22/0.58  % (15365)Time elapsed: 0.133 s
% 0.22/0.58  % (15365)------------------------------
% 0.22/0.58  % (15365)------------------------------
% 2.05/0.70  % (15465)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.05/0.70  % (15482)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.05/0.71  % (15484)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.05/0.72  % (15477)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.25/0.81  % (15369)Refutation found. Thanks to Tanya!
% 3.25/0.81  % SZS status Theorem for theBenchmark
% 3.25/0.81  % SZS output start Proof for theBenchmark
% 3.25/0.81  fof(f2589,plain,(
% 3.25/0.81    $false),
% 3.25/0.81    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f209,f354,f774,f825,f2588])).
% 3.25/0.81  fof(f2588,plain,(
% 3.25/0.81    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 3.25/0.81    inference(avatar_contradiction_clause,[],[f2587])).
% 3.25/0.81  fof(f2587,plain,(
% 3.25/0.81    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.25/0.81    inference(subsumption_resolution,[],[f2586,f928])).
% 3.25/0.81  fof(f928,plain,(
% 3.25/0.81    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f131,f854])).
% 3.25/0.81  fof(f854,plain,(
% 3.25/0.81    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 3.25/0.81    inference(superposition,[],[f116,f826])).
% 3.25/0.81  fof(f826,plain,(
% 3.25/0.81    sK0 = k3_tarski(sK0) | ~spl8_1),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f121,f78])).
% 3.25/0.81  fof(f78,plain,(
% 3.25/0.81    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 3.25/0.81    inference(cnf_transformation,[],[f46])).
% 3.25/0.81  fof(f46,plain,(
% 3.25/0.81    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 3.25/0.81    inference(nnf_transformation,[],[f6])).
% 3.25/0.81  fof(f6,axiom,(
% 3.25/0.81    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).
% 3.25/0.81  fof(f121,plain,(
% 3.25/0.81    v4_ordinal1(sK0) | ~spl8_1),
% 3.25/0.81    inference(avatar_component_clause,[],[f120])).
% 3.25/0.81  fof(f120,plain,(
% 3.25/0.81    spl8_1 <=> v4_ordinal1(sK0)),
% 3.25/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.25/0.81  fof(f116,plain,(
% 3.25/0.81    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.25/0.81    inference(equality_resolution,[],[f94])).
% 3.25/0.81  fof(f94,plain,(
% 3.25/0.81    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.25/0.81    inference(cnf_transformation,[],[f61])).
% 3.25/0.81  fof(f61,plain,(
% 3.25/0.81    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.25/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f60,f59,f58])).
% 3.25/0.81  fof(f58,plain,(
% 3.25/0.81    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 3.25/0.81    introduced(choice_axiom,[])).
% 3.25/0.81  fof(f59,plain,(
% 3.25/0.81    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 3.25/0.81    introduced(choice_axiom,[])).
% 3.25/0.81  fof(f60,plain,(
% 3.25/0.81    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 3.25/0.81    introduced(choice_axiom,[])).
% 3.25/0.81  fof(f57,plain,(
% 3.25/0.81    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.25/0.81    inference(rectify,[],[f56])).
% 3.25/0.81  fof(f56,plain,(
% 3.25/0.81    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.25/0.81    inference(nnf_transformation,[],[f3])).
% 3.25/0.81  fof(f3,axiom,(
% 3.25/0.81    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 3.25/0.81  fof(f131,plain,(
% 3.25/0.81    r2_hidden(sK1,sK0) | ~spl8_3),
% 3.25/0.81    inference(avatar_component_clause,[],[f129])).
% 3.25/0.81  fof(f129,plain,(
% 3.25/0.81    spl8_3 <=> r2_hidden(sK1,sK0)),
% 3.25/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.25/0.81  fof(f2586,plain,(
% 3.25/0.81    ~r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.25/0.81    inference(forward_demodulation,[],[f2585,f1146])).
% 3.25/0.81  fof(f1146,plain,(
% 3.25/0.81    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f64,f215,f126,f887,f75])).
% 3.25/0.81  fof(f75,plain,(
% 3.25/0.81    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.81    inference(cnf_transformation,[],[f25])).
% 3.25/0.81  fof(f25,plain,(
% 3.25/0.81    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(flattening,[],[f24])).
% 3.25/0.81  fof(f24,plain,(
% 3.25/0.81    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(ennf_transformation,[],[f12])).
% 3.25/0.81  fof(f12,axiom,(
% 3.25/0.81    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 3.25/0.81  fof(f887,plain,(
% 3.25/0.81    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_3 | ~spl8_4)),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f64,f136,f842,f109])).
% 3.25/0.81  fof(f109,plain,(
% 3.25/0.81    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.81    inference(definition_unfolding,[],[f73,f71])).
% 3.25/0.81  fof(f71,plain,(
% 3.25/0.81    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.25/0.81    inference(cnf_transformation,[],[f5])).
% 3.25/0.81  fof(f5,axiom,(
% 3.25/0.81    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 3.25/0.81  fof(f73,plain,(
% 3.25/0.81    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.81    inference(cnf_transformation,[],[f43])).
% 3.25/0.81  fof(f43,plain,(
% 3.25/0.81    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(nnf_transformation,[],[f23])).
% 3.25/0.81  fof(f23,plain,(
% 3.25/0.81    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(ennf_transformation,[],[f14])).
% 3.25/0.81  fof(f14,axiom,(
% 3.25/0.81    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 3.25/0.81  fof(f842,plain,(
% 3.25/0.81    ~r1_ordinal1(sK0,sK1) | (~spl8_3 | ~spl8_4)),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f64,f136,f833,f85])).
% 3.25/0.81  fof(f85,plain,(
% 3.25/0.81    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.81    inference(cnf_transformation,[],[f49])).
% 3.25/0.81  fof(f49,plain,(
% 3.25/0.81    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(nnf_transformation,[],[f34])).
% 3.25/0.81  fof(f34,plain,(
% 3.25/0.81    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(flattening,[],[f33])).
% 3.25/0.81  fof(f33,plain,(
% 3.25/0.81    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.25/0.81    inference(ennf_transformation,[],[f7])).
% 3.25/0.81  fof(f7,axiom,(
% 3.25/0.81    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 3.25/0.81  fof(f833,plain,(
% 3.25/0.81    ~r1_tarski(sK0,sK1) | ~spl8_3),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f131,f102])).
% 3.25/0.81  fof(f102,plain,(
% 3.25/0.81    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.25/0.81    inference(cnf_transformation,[],[f36])).
% 3.25/0.81  fof(f36,plain,(
% 3.25/0.81    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.25/0.81    inference(ennf_transformation,[],[f17])).
% 3.25/0.81  fof(f17,axiom,(
% 3.25/0.81    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.25/0.81  fof(f136,plain,(
% 3.25/0.81    v3_ordinal1(sK1) | ~spl8_4),
% 3.25/0.81    inference(avatar_component_clause,[],[f134])).
% 3.25/0.81  fof(f134,plain,(
% 3.25/0.81    spl8_4 <=> v3_ordinal1(sK1)),
% 3.25/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.25/0.81  fof(f126,plain,(
% 3.25/0.81    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 3.25/0.81    inference(avatar_component_clause,[],[f124])).
% 3.25/0.81  fof(f124,plain,(
% 3.25/0.81    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 3.25/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.25/0.81  fof(f215,plain,(
% 3.25/0.81    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 3.25/0.81    inference(unit_resulting_resolution,[],[f136,f107])).
% 3.25/0.81  fof(f107,plain,(
% 3.25/0.81    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.25/0.81    inference(definition_unfolding,[],[f72,f71])).
% 3.25/0.81  fof(f72,plain,(
% 3.25/0.81    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.25/0.81    inference(cnf_transformation,[],[f22])).
% 3.25/0.81  fof(f22,plain,(
% 3.25/0.81    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.25/0.81    inference(ennf_transformation,[],[f13])).
% 3.25/0.81  fof(f13,axiom,(
% 3.25/0.81    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.25/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 3.25/0.82  fof(f64,plain,(
% 3.25/0.82    v3_ordinal1(sK0)),
% 3.25/0.82    inference(cnf_transformation,[],[f42])).
% 3.25/0.82  fof(f42,plain,(
% 3.25/0.82    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 3.25/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 3.25/0.82  fof(f40,plain,(
% 3.25/0.82    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 3.25/0.82    introduced(choice_axiom,[])).
% 3.25/0.82  fof(f41,plain,(
% 3.25/0.82    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 3.25/0.82    introduced(choice_axiom,[])).
% 3.25/0.82  fof(f39,plain,(
% 3.25/0.82    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.25/0.82    inference(rectify,[],[f38])).
% 3.25/0.82  fof(f38,plain,(
% 3.25/0.82    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.25/0.82    inference(flattening,[],[f37])).
% 3.25/0.82  fof(f37,plain,(
% 3.25/0.82    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.25/0.82    inference(nnf_transformation,[],[f21])).
% 3.25/0.82  fof(f21,plain,(
% 3.25/0.82    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.25/0.82    inference(flattening,[],[f20])).
% 3.25/0.82  fof(f20,plain,(
% 3.25/0.82    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.25/0.82    inference(ennf_transformation,[],[f19])).
% 3.25/0.82  fof(f19,negated_conjecture,(
% 3.25/0.82    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.25/0.82    inference(negated_conjecture,[],[f18])).
% 3.25/0.82  fof(f18,conjecture,(
% 3.25/0.82    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.25/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 3.25/0.82  fof(f2585,plain,(
% 3.25/0.82    ~r2_hidden(sK7(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f136,f1115,f2093,f109])).
% 3.25/0.82  fof(f2093,plain,(
% 3.25/0.82    ~r1_ordinal1(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f136,f1115,f1128,f85])).
% 3.25/0.82  fof(f1128,plain,(
% 3.25/0.82    ~r1_tarski(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f931,f102])).
% 3.25/0.82  fof(f931,plain,(
% 3.25/0.82    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f131,f855])).
% 3.25/0.82  fof(f855,plain,(
% 3.25/0.82    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 3.25/0.82    inference(superposition,[],[f117,f826])).
% 3.25/0.82  fof(f117,plain,(
% 3.25/0.82    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.25/0.82    inference(equality_resolution,[],[f93])).
% 3.25/0.82  fof(f93,plain,(
% 3.25/0.82    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.25/0.82    inference(cnf_transformation,[],[f61])).
% 3.25/0.82  fof(f1115,plain,(
% 3.25/0.82    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f64,f928,f83])).
% 3.25/0.82  fof(f83,plain,(
% 3.25/0.82    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f30])).
% 3.25/0.82  fof(f30,plain,(
% 3.25/0.82    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.25/0.82    inference(flattening,[],[f29])).
% 3.25/0.82  fof(f29,plain,(
% 3.25/0.82    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.25/0.82    inference(ennf_transformation,[],[f11])).
% 3.25/0.82  fof(f11,axiom,(
% 3.25/0.82    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.25/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 3.25/0.82  fof(f825,plain,(
% 3.25/0.82    spl8_1 | ~spl8_5 | ~spl8_6),
% 3.25/0.82    inference(avatar_contradiction_clause,[],[f824])).
% 3.25/0.82  fof(f824,plain,(
% 3.25/0.82    $false | (spl8_1 | ~spl8_5 | ~spl8_6)),
% 3.25/0.82    inference(subsumption_resolution,[],[f823,f779])).
% 3.25/0.82  fof(f779,plain,(
% 3.25/0.82    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_6)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f234,f106,f204,f98])).
% 3.25/0.82  fof(f98,plain,(
% 3.25/0.82    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f61])).
% 3.25/0.82  fof(f204,plain,(
% 3.25/0.82    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_6),
% 3.25/0.82    inference(avatar_component_clause,[],[f202])).
% 3.25/0.82  fof(f202,plain,(
% 3.25/0.82    spl8_6 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 3.25/0.82    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.25/0.82  fof(f106,plain,(
% 3.25/0.82    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 3.25/0.82    inference(definition_unfolding,[],[f70,f71])).
% 3.25/0.82  fof(f70,plain,(
% 3.25/0.82    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.25/0.82    inference(cnf_transformation,[],[f8])).
% 3.25/0.82  fof(f8,axiom,(
% 3.25/0.82    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.25/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 3.25/0.82  fof(f234,plain,(
% 3.25/0.82    sK0 != k3_tarski(sK0) | spl8_1),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f122,f79])).
% 3.25/0.82  fof(f79,plain,(
% 3.25/0.82    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 3.25/0.82    inference(cnf_transformation,[],[f46])).
% 3.25/0.82  fof(f122,plain,(
% 3.25/0.82    ~v4_ordinal1(sK0) | spl8_1),
% 3.25/0.82    inference(avatar_component_clause,[],[f120])).
% 3.25/0.82  fof(f823,plain,(
% 3.25/0.82    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_6)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f204,f782,f140])).
% 3.25/0.82  fof(f140,plain,(
% 3.25/0.82    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 3.25/0.82    inference(avatar_component_clause,[],[f139])).
% 3.25/0.82  fof(f139,plain,(
% 3.25/0.82    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 3.25/0.82    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.25/0.82  fof(f782,plain,(
% 3.25/0.82    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_6),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f64,f204,f83])).
% 3.25/0.82  fof(f774,plain,(
% 3.25/0.82    spl8_6 | ~spl8_7 | ~spl8_8),
% 3.25/0.82    inference(avatar_contradiction_clause,[],[f773])).
% 3.25/0.82  fof(f773,plain,(
% 3.25/0.82    $false | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 3.25/0.82    inference(subsumption_resolution,[],[f763,f640])).
% 3.25/0.82  fof(f640,plain,(
% 3.25/0.82    ~r1_ordinal1(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f64,f335,f425,f85])).
% 3.25/0.82  fof(f425,plain,(
% 3.25/0.82    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_8)),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f203,f353,f90])).
% 3.25/0.82  fof(f90,plain,(
% 3.25/0.82    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f55])).
% 3.25/0.82  fof(f55,plain,(
% 3.25/0.82    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).
% 3.25/0.82  fof(f54,plain,(
% 3.25/0.82    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.25/0.82    introduced(choice_axiom,[])).
% 3.25/0.82  fof(f53,plain,(
% 3.25/0.82    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/0.82    inference(rectify,[],[f52])).
% 3.25/0.82  fof(f52,plain,(
% 3.25/0.82    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/0.82    inference(nnf_transformation,[],[f35])).
% 3.25/0.82  fof(f35,plain,(
% 3.25/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.25/0.82    inference(ennf_transformation,[],[f1])).
% 3.25/0.82  fof(f1,axiom,(
% 3.25/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.25/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.25/0.82  fof(f353,plain,(
% 3.25/0.82    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_8),
% 3.25/0.82    inference(avatar_component_clause,[],[f351])).
% 3.25/0.82  fof(f351,plain,(
% 3.25/0.82    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 3.25/0.82    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.25/0.82  fof(f203,plain,(
% 3.25/0.82    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_6),
% 3.25/0.82    inference(avatar_component_clause,[],[f202])).
% 3.25/0.82  fof(f335,plain,(
% 3.25/0.82    v3_ordinal1(sK6(sK0,sK0)) | ~spl8_7),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f64,f208,f83])).
% 3.25/0.82  fof(f208,plain,(
% 3.25/0.82    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_7),
% 3.25/0.82    inference(avatar_component_clause,[],[f206])).
% 3.25/0.82  fof(f206,plain,(
% 3.25/0.82    spl8_7 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 3.25/0.82    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.25/0.82  fof(f763,plain,(
% 3.25/0.82    r1_ordinal1(sK6(sK0,sK0),sK0) | ~spl8_7),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f64,f335,f340,f109])).
% 3.25/0.82  fof(f340,plain,(
% 3.25/0.82    r2_hidden(sK6(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl8_7),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f208,f111])).
% 3.25/0.82  fof(f111,plain,(
% 3.25/0.82    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 3.25/0.82    inference(definition_unfolding,[],[f100,f71])).
% 3.25/0.82  fof(f100,plain,(
% 3.25/0.82    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f63])).
% 3.25/0.82  fof(f63,plain,(
% 3.25/0.82    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.25/0.82    inference(flattening,[],[f62])).
% 3.25/0.82  fof(f62,plain,(
% 3.25/0.82    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.25/0.82    inference(nnf_transformation,[],[f9])).
% 3.25/0.82  fof(f9,axiom,(
% 3.25/0.82    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.25/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 3.25/0.82  fof(f354,plain,(
% 3.25/0.82    spl8_6 | spl8_8 | spl8_1),
% 3.25/0.82    inference(avatar_split_clause,[],[f349,f120,f351,f202])).
% 3.25/0.82  fof(f349,plain,(
% 3.25/0.82    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 3.25/0.82    inference(equality_resolution,[],[f248])).
% 3.25/0.82  fof(f248,plain,(
% 3.25/0.82    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 3.25/0.82    inference(superposition,[],[f234,f96])).
% 3.25/0.82  fof(f96,plain,(
% 3.25/0.82    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f61])).
% 3.25/0.82  fof(f209,plain,(
% 3.25/0.82    spl8_6 | spl8_7 | spl8_1),
% 3.25/0.82    inference(avatar_split_clause,[],[f200,f120,f206,f202])).
% 3.25/0.82  fof(f200,plain,(
% 3.25/0.82    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 3.25/0.82    inference(equality_resolution,[],[f157])).
% 3.25/0.82  fof(f157,plain,(
% 3.25/0.82    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 3.25/0.82    inference(superposition,[],[f152,f97])).
% 3.25/0.82  fof(f97,plain,(
% 3.25/0.82    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f61])).
% 3.25/0.82  fof(f152,plain,(
% 3.25/0.82    sK0 != k3_tarski(sK0) | spl8_1),
% 3.25/0.82    inference(unit_resulting_resolution,[],[f122,f79])).
% 3.25/0.82  fof(f141,plain,(
% 3.25/0.82    spl8_1 | spl8_5),
% 3.25/0.82    inference(avatar_split_clause,[],[f104,f139,f120])).
% 3.25/0.82  fof(f104,plain,(
% 3.25/0.82    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.25/0.82    inference(definition_unfolding,[],[f65,f71])).
% 3.25/0.82  fof(f65,plain,(
% 3.25/0.82    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.25/0.82    inference(cnf_transformation,[],[f42])).
% 3.25/0.82  fof(f137,plain,(
% 3.25/0.82    ~spl8_1 | spl8_4),
% 3.25/0.82    inference(avatar_split_clause,[],[f66,f134,f120])).
% 3.25/0.82  fof(f66,plain,(
% 3.25/0.82    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 3.25/0.82    inference(cnf_transformation,[],[f42])).
% 3.25/0.82  fof(f132,plain,(
% 3.25/0.82    ~spl8_1 | spl8_3),
% 3.25/0.82    inference(avatar_split_clause,[],[f67,f129,f120])).
% 3.25/0.82  fof(f67,plain,(
% 3.25/0.82    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 3.25/0.82    inference(cnf_transformation,[],[f42])).
% 3.25/0.82  fof(f127,plain,(
% 3.25/0.82    ~spl8_1 | ~spl8_2),
% 3.25/0.82    inference(avatar_split_clause,[],[f103,f124,f120])).
% 3.25/0.82  fof(f103,plain,(
% 3.25/0.82    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 3.25/0.82    inference(definition_unfolding,[],[f68,f71])).
% 3.25/0.82  fof(f68,plain,(
% 3.25/0.82    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 3.25/0.82    inference(cnf_transformation,[],[f42])).
% 3.25/0.82  % SZS output end Proof for theBenchmark
% 3.25/0.82  % (15369)------------------------------
% 3.25/0.82  % (15369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.82  % (15369)Termination reason: Refutation
% 3.25/0.82  
% 3.25/0.82  % (15369)Memory used [KB]: 12537
% 3.25/0.82  % (15369)Time elapsed: 0.381 s
% 3.25/0.82  % (15369)------------------------------
% 3.25/0.82  % (15369)------------------------------
% 3.25/0.82  % (15338)Success in time 0.457 s
%------------------------------------------------------------------------------
