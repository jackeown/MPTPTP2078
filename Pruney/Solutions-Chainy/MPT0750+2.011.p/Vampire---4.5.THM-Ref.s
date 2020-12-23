%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:41 EST 2020

% Result     : Theorem 5.47s
% Output     : Refutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 452 expanded)
%              Number of leaves         :   27 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  502 (2288 expanded)
%              Number of equality atoms :   33 ( 119 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f139,f144,f148,f276,f445,f454,f3295,f6356])).

fof(f6356,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f6355])).

fof(f6355,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f6354,f3624])).

fof(f3624,plain,
    ( r2_hidden(sK9(sK0,sK1),sK0)
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f138,f3349])).

fof(f3349,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK9(sK0,X6),sK0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f123,f3296])).

fof(f3296,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f128,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f128,plain,
    ( v4_ordinal1(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f123,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK9(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK9(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK7(X0,X1),X3) )
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( ( r2_hidden(sK8(X0,X1),X0)
              & r2_hidden(sK7(X0,X1),sK8(X0,X1)) )
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK9(X0,X5),X0)
                & r2_hidden(X5,sK9(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).

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
              | ~ r2_hidden(sK7(X0,X1),X3) )
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK7(X0,X1),X4) )
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK7(X0,X1),X4) )
     => ( r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK7(X0,X1),sK8(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK9(X0,X5),X0)
        & r2_hidden(X5,sK9(X0,X5)) ) ) ),
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

fof(f138,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f6354,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f6353,f4125])).

fof(f4125,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f69,f3303,f133,f3370,f79])).

fof(f79,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f3370,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f69,f143,f3337,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f77,f75])).

fof(f75,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f3337,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f69,f143,f3314,f93])).

fof(f93,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f3314,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f138,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f143,plain,
    ( v3_ordinal1(sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f133,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl10_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f3303,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f143,f114])).

fof(f114,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f76,plain,(
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

fof(f69,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f6353,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f143,f4071,f5378,f116])).

fof(f5378,plain,
    ( ~ r1_ordinal1(sK9(sK0,sK1),sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f143,f4071,f4096,f93])).

fof(f4096,plain,
    ( ~ r1_tarski(sK9(sK0,sK1),sK1)
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f3626,f110])).

fof(f3626,plain,
    ( r2_hidden(sK1,sK9(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f138,f3350])).

fof(f3350,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK9(sK0,X7)) )
    | ~ spl10_1 ),
    inference(superposition,[],[f124,f3296])).

fof(f124,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK9(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK9(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f4071,plain,
    ( v3_ordinal1(sK9(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f69,f3624,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f3295,plain,
    ( spl10_8
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f3294])).

fof(f3294,plain,
    ( $false
    | spl10_8
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f3293,f2702])).

fof(f2702,plain,
    ( r2_hidden(sK8(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f275,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f108,f75])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
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

fof(f275,plain,
    ( r2_hidden(sK8(sK0,sK0),sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl10_9
  <=> r2_hidden(sK8(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f3293,plain,
    ( ~ r2_hidden(sK8(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl10_8
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f69,f2698,f2982,f116])).

fof(f2982,plain,
    ( ~ r1_ordinal1(sK8(sK0,sK0),sK0)
    | spl10_8
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f69,f2698,f2828,f93])).

fof(f2828,plain,
    ( ~ r1_tarski(sK8(sK0,sK0),sK0)
    | spl10_8
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f270,f453,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f453,plain,
    ( r2_hidden(sK7(sK0,sK0),sK8(sK0,sK0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl10_13
  <=> r2_hidden(sK7(sK0,sK0),sK8(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f270,plain,
    ( ~ r2_hidden(sK7(sK0,sK0),sK0)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl10_8
  <=> r2_hidden(sK7(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f2698,plain,
    ( v3_ordinal1(sK8(sK0,sK0))
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f69,f275,f92])).

fof(f454,plain,
    ( spl10_8
    | spl10_13
    | spl10_1 ),
    inference(avatar_split_clause,[],[f304,f127,f451,f269])).

fof(f304,plain,
    ( r2_hidden(sK7(sK0,sK0),sK8(sK0,sK0))
    | r2_hidden(sK7(sK0,sK0),sK0)
    | spl10_1 ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK7(sK0,X0),sK8(sK0,X0))
        | r2_hidden(sK7(sK0,X0),X0) )
    | spl10_1 ),
    inference(superposition,[],[f162,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK7(X0,X1),sK8(X0,X1))
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f162,plain,
    ( sK0 != k3_tarski(sK0)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f129,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f129,plain,
    ( ~ v4_ordinal1(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f445,plain,
    ( spl10_1
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | spl10_1
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f443,f290])).

fof(f290,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7(sK0,sK0),k1_tarski(sK7(sK0,sK0))),sK0)
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f162,f113,f271,f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK7(X0,X1),X3)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f271,plain,
    ( r2_hidden(sK7(sK0,sK0),sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f269])).

fof(f113,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f443,plain,
    ( r2_hidden(k2_xboole_0(sK7(sK0,sK0),k1_tarski(sK7(sK0,sK0))),sK0)
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f271,f291,f147])).

fof(f147,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl10_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f291,plain,
    ( v3_ordinal1(sK7(sK0,sK0))
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f69,f271,f92])).

fof(f276,plain,
    ( spl10_8
    | spl10_9
    | spl10_1 ),
    inference(avatar_split_clause,[],[f267,f127,f273,f269])).

fof(f267,plain,
    ( r2_hidden(sK8(sK0,sK0),sK0)
    | r2_hidden(sK7(sK0,sK0),sK0)
    | spl10_1 ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK8(sK0,X1),sK0)
        | r2_hidden(sK7(sK0,X1),X1) )
    | spl10_1 ),
    inference(superposition,[],[f162,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK8(X0,X1),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f148,plain,
    ( spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f112,f146,f127])).

fof(f112,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f144,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f71,f141,f127])).

fof(f71,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f139,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f72,f136,f127])).

fof(f72,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f134,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f111,f131,f127])).

fof(f111,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f73,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (27325)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (27317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (27328)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (27336)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (27346)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (27326)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (27322)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27327)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (27333)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (27340)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (27332)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (27338)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (27340)Refutation not found, incomplete strategy% (27340)------------------------------
% 0.21/0.53  % (27340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27340)Memory used [KB]: 10746
% 0.21/0.53  % (27340)Time elapsed: 0.086 s
% 0.21/0.53  % (27340)------------------------------
% 0.21/0.53  % (27340)------------------------------
% 0.21/0.53  % (27321)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (27318)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (27347)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (27330)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (27323)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (27324)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (27335)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (27319)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (27344)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (27319)Refutation not found, incomplete strategy% (27319)------------------------------
% 0.21/0.53  % (27319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27319)Memory used [KB]: 10746
% 0.21/0.53  % (27319)Time elapsed: 0.128 s
% 0.21/0.53  % (27319)------------------------------
% 0.21/0.53  % (27319)------------------------------
% 0.21/0.54  % (27341)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (27345)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27339)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (27339)Refutation not found, incomplete strategy% (27339)------------------------------
% 0.21/0.54  % (27339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27339)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27339)Memory used [KB]: 1663
% 0.21/0.54  % (27339)Time elapsed: 0.129 s
% 0.21/0.54  % (27339)------------------------------
% 0.21/0.54  % (27339)------------------------------
% 0.21/0.54  % (27343)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (27337)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (27331)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (27334)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (27338)Refutation not found, incomplete strategy% (27338)------------------------------
% 0.21/0.54  % (27338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27338)Memory used [KB]: 10746
% 0.21/0.54  % (27338)Time elapsed: 0.143 s
% 0.21/0.54  % (27338)------------------------------
% 0.21/0.54  % (27338)------------------------------
% 0.21/0.55  % (27342)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (27329)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.10/0.67  % (27349)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.68  % (27351)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.68  % (27348)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.69  % (27350)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.39/0.81  % (27323)Time limit reached!
% 3.39/0.81  % (27323)------------------------------
% 3.39/0.81  % (27323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.81  % (27323)Termination reason: Time limit
% 3.39/0.81  
% 3.39/0.81  % (27323)Memory used [KB]: 9338
% 3.39/0.81  % (27323)Time elapsed: 0.410 s
% 3.39/0.81  % (27323)------------------------------
% 3.39/0.81  % (27323)------------------------------
% 4.24/0.91  % (27328)Time limit reached!
% 4.24/0.91  % (27328)------------------------------
% 4.24/0.91  % (27328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.91  % (27328)Termination reason: Time limit
% 4.24/0.91  % (27328)Termination phase: Saturation
% 4.24/0.91  
% 4.24/0.91  % (27328)Memory used [KB]: 15479
% 4.24/0.91  % (27328)Time elapsed: 0.503 s
% 4.24/0.91  % (27328)------------------------------
% 4.24/0.91  % (27328)------------------------------
% 4.24/0.92  % (27317)Time limit reached!
% 4.24/0.92  % (27317)------------------------------
% 4.24/0.92  % (27317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.92  % (27317)Termination reason: Time limit
% 4.24/0.92  
% 4.24/0.92  % (27317)Memory used [KB]: 4605
% 4.24/0.92  % (27317)Time elapsed: 0.507 s
% 4.24/0.92  % (27317)------------------------------
% 4.24/0.92  % (27317)------------------------------
% 4.24/0.92  % (27335)Time limit reached!
% 4.24/0.92  % (27335)------------------------------
% 4.24/0.92  % (27335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.92  % (27335)Termination reason: Time limit
% 4.24/0.92  
% 4.24/0.92  % (27335)Memory used [KB]: 14711
% 4.24/0.92  % (27335)Time elapsed: 0.513 s
% 4.24/0.92  % (27335)------------------------------
% 4.24/0.92  % (27335)------------------------------
% 4.24/0.92  % (27318)Time limit reached!
% 4.24/0.92  % (27318)------------------------------
% 4.24/0.92  % (27318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.92  % (27318)Termination reason: Time limit
% 4.24/0.92  
% 4.24/0.92  % (27318)Memory used [KB]: 8059
% 4.24/0.92  % (27318)Time elapsed: 0.510 s
% 4.24/0.92  % (27318)------------------------------
% 4.24/0.92  % (27318)------------------------------
% 4.45/0.94  % (27330)Time limit reached!
% 4.45/0.94  % (27330)------------------------------
% 4.45/0.94  % (27330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.94  % (27330)Termination reason: Time limit
% 4.45/0.94  % (27330)Termination phase: Saturation
% 4.45/0.94  
% 4.45/0.94  % (27330)Memory used [KB]: 8827
% 4.45/0.94  % (27330)Time elapsed: 0.535 s
% 4.45/0.94  % (27330)------------------------------
% 4.45/0.94  % (27330)------------------------------
% 4.45/0.94  % (27353)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.45/0.99  % (27351)Time limit reached!
% 4.45/0.99  % (27351)------------------------------
% 4.45/0.99  % (27351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.99  % (27351)Termination reason: Time limit
% 4.45/0.99  
% 4.45/0.99  % (27351)Memory used [KB]: 6780
% 4.45/0.99  % (27351)Time elapsed: 0.418 s
% 4.45/0.99  % (27351)------------------------------
% 4.45/0.99  % (27351)------------------------------
% 4.45/1.02  % (27325)Time limit reached!
% 4.45/1.02  % (27325)------------------------------
% 4.45/1.02  % (27325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.02  % (27325)Termination reason: Time limit
% 4.45/1.02  % (27325)Termination phase: Saturation
% 4.45/1.02  
% 4.45/1.02  % (27325)Memory used [KB]: 13048
% 4.45/1.02  % (27325)Time elapsed: 0.605 s
% 4.45/1.02  % (27325)------------------------------
% 4.45/1.02  % (27325)------------------------------
% 5.07/1.03  % (27346)Time limit reached!
% 5.07/1.03  % (27346)------------------------------
% 5.07/1.03  % (27346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.03  % (27346)Termination reason: Time limit
% 5.07/1.03  
% 5.07/1.03  % (27346)Memory used [KB]: 9978
% 5.07/1.03  % (27346)Time elapsed: 0.625 s
% 5.07/1.03  % (27346)------------------------------
% 5.07/1.03  % (27346)------------------------------
% 5.07/1.03  % (27334)Time limit reached!
% 5.07/1.03  % (27334)------------------------------
% 5.07/1.03  % (27334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.03  % (27334)Termination reason: Time limit
% 5.07/1.03  
% 5.07/1.03  % (27334)Memory used [KB]: 17398
% 5.07/1.03  % (27334)Time elapsed: 0.632 s
% 5.07/1.03  % (27334)------------------------------
% 5.07/1.03  % (27334)------------------------------
% 5.07/1.03  % (27354)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.07/1.04  % (27355)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.07/1.05  % (27357)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.07/1.06  % (27356)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.07/1.07  % (27358)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.47/1.10  % (27344)Refutation found. Thanks to Tanya!
% 5.47/1.10  % SZS status Theorem for theBenchmark
% 5.47/1.10  % SZS output start Proof for theBenchmark
% 5.47/1.10  fof(f6357,plain,(
% 5.47/1.10    $false),
% 5.47/1.10    inference(avatar_sat_refutation,[],[f134,f139,f144,f148,f276,f445,f454,f3295,f6356])).
% 5.47/1.10  fof(f6356,plain,(
% 5.47/1.10    ~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_4),
% 5.47/1.10    inference(avatar_contradiction_clause,[],[f6355])).
% 5.47/1.10  fof(f6355,plain,(
% 5.47/1.10    $false | (~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_4)),
% 5.47/1.10    inference(subsumption_resolution,[],[f6354,f3624])).
% 5.47/1.10  fof(f3624,plain,(
% 5.47/1.10    r2_hidden(sK9(sK0,sK1),sK0) | (~spl10_1 | ~spl10_3)),
% 5.47/1.10    inference(unit_resulting_resolution,[],[f138,f3349])).
% 5.47/1.10  fof(f3349,plain,(
% 5.47/1.10    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK9(sK0,X6),sK0)) ) | ~spl10_1),
% 5.47/1.10    inference(superposition,[],[f123,f3296])).
% 5.47/1.10  fof(f3296,plain,(
% 5.47/1.10    sK0 = k3_tarski(sK0) | ~spl10_1),
% 5.47/1.10    inference(unit_resulting_resolution,[],[f128,f82])).
% 5.47/1.10  fof(f82,plain,(
% 5.47/1.10    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 5.47/1.10    inference(cnf_transformation,[],[f45])).
% 5.47/1.10  fof(f45,plain,(
% 5.47/1.10    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 5.47/1.10    inference(nnf_transformation,[],[f5])).
% 5.47/1.10  fof(f5,axiom,(
% 5.47/1.10    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 5.47/1.10  fof(f128,plain,(
% 5.47/1.10    v4_ordinal1(sK0) | ~spl10_1),
% 5.47/1.10    inference(avatar_component_clause,[],[f127])).
% 5.47/1.10  fof(f127,plain,(
% 5.47/1.10    spl10_1 <=> v4_ordinal1(sK0)),
% 5.47/1.10    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 5.47/1.10  fof(f123,plain,(
% 5.47/1.10    ( ! [X0,X5] : (r2_hidden(sK9(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 5.47/1.10    inference(equality_resolution,[],[f102])).
% 5.47/1.10  fof(f102,plain,(
% 5.47/1.10    ( ! [X0,X5,X1] : (r2_hidden(sK9(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 5.47/1.10    inference(cnf_transformation,[],[f66])).
% 5.47/1.10  fof(f66,plain,(
% 5.47/1.10    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK7(X0,X1),X3)) | ~r2_hidden(sK7(X0,X1),X1)) & ((r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK7(X0,X1),sK8(X0,X1))) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK9(X0,X5),X0) & r2_hidden(X5,sK9(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 5.47/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).
% 5.47/1.10  fof(f63,plain,(
% 5.47/1.10    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK7(X0,X1),X3)) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK7(X0,X1),X4)) | r2_hidden(sK7(X0,X1),X1))))),
% 5.47/1.10    introduced(choice_axiom,[])).
% 5.47/1.10  fof(f64,plain,(
% 5.47/1.10    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK7(X0,X1),X4)) => (r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK7(X0,X1),sK8(X0,X1))))),
% 5.47/1.10    introduced(choice_axiom,[])).
% 5.47/1.10  fof(f65,plain,(
% 5.47/1.10    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK9(X0,X5),X0) & r2_hidden(X5,sK9(X0,X5))))),
% 5.47/1.10    introduced(choice_axiom,[])).
% 5.47/1.10  fof(f62,plain,(
% 5.47/1.10    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 5.47/1.10    inference(rectify,[],[f61])).
% 5.47/1.10  fof(f61,plain,(
% 5.47/1.10    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 5.47/1.10    inference(nnf_transformation,[],[f3])).
% 5.47/1.10  fof(f3,axiom,(
% 5.47/1.10    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 5.47/1.10  fof(f138,plain,(
% 5.47/1.10    r2_hidden(sK1,sK0) | ~spl10_3),
% 5.47/1.10    inference(avatar_component_clause,[],[f136])).
% 5.47/1.10  fof(f136,plain,(
% 5.47/1.10    spl10_3 <=> r2_hidden(sK1,sK0)),
% 5.47/1.10    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 5.47/1.10  fof(f6354,plain,(
% 5.47/1.10    ~r2_hidden(sK9(sK0,sK1),sK0) | (~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_4)),
% 5.47/1.10    inference(forward_demodulation,[],[f6353,f4125])).
% 5.47/1.10  fof(f4125,plain,(
% 5.47/1.10    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl10_2 | ~spl10_3 | ~spl10_4)),
% 5.47/1.10    inference(unit_resulting_resolution,[],[f69,f3303,f133,f3370,f79])).
% 5.47/1.10  fof(f79,plain,(
% 5.47/1.10    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 5.47/1.10    inference(cnf_transformation,[],[f25])).
% 5.47/1.10  fof(f25,plain,(
% 5.47/1.10    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 5.47/1.10    inference(flattening,[],[f24])).
% 5.47/1.10  fof(f24,plain,(
% 5.47/1.10    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 5.47/1.10    inference(ennf_transformation,[],[f11])).
% 5.47/1.10  fof(f11,axiom,(
% 5.47/1.10    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 5.47/1.10  fof(f3370,plain,(
% 5.47/1.10    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl10_3 | ~spl10_4)),
% 5.47/1.10    inference(unit_resulting_resolution,[],[f69,f143,f3337,f116])).
% 5.47/1.10  fof(f116,plain,(
% 5.47/1.10    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 5.47/1.10    inference(definition_unfolding,[],[f77,f75])).
% 5.47/1.10  fof(f75,plain,(
% 5.47/1.10    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 5.47/1.10    inference(cnf_transformation,[],[f4])).
% 5.47/1.10  fof(f4,axiom,(
% 5.47/1.10    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 5.47/1.10  fof(f77,plain,(
% 5.47/1.10    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 5.47/1.10    inference(cnf_transformation,[],[f42])).
% 5.47/1.10  fof(f42,plain,(
% 5.47/1.10    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 5.47/1.10    inference(nnf_transformation,[],[f23])).
% 5.47/1.10  fof(f23,plain,(
% 5.47/1.10    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 5.47/1.10    inference(ennf_transformation,[],[f13])).
% 5.47/1.10  fof(f13,axiom,(
% 5.47/1.10    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 5.47/1.10  fof(f3337,plain,(
% 5.47/1.10    ~r1_ordinal1(sK0,sK1) | (~spl10_3 | ~spl10_4)),
% 5.47/1.10    inference(unit_resulting_resolution,[],[f69,f143,f3314,f93])).
% 5.47/1.10  fof(f93,plain,(
% 5.47/1.10    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 5.47/1.10    inference(cnf_transformation,[],[f54])).
% 5.47/1.10  fof(f54,plain,(
% 5.47/1.10    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 5.47/1.10    inference(nnf_transformation,[],[f33])).
% 5.47/1.10  fof(f33,plain,(
% 5.47/1.10    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 5.47/1.10    inference(flattening,[],[f32])).
% 5.47/1.10  fof(f32,plain,(
% 5.47/1.10    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 5.47/1.10    inference(ennf_transformation,[],[f6])).
% 5.47/1.10  fof(f6,axiom,(
% 5.47/1.10    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 5.47/1.10  fof(f3314,plain,(
% 5.47/1.10    ~r1_tarski(sK0,sK1) | ~spl10_3),
% 5.47/1.10    inference(unit_resulting_resolution,[],[f138,f110])).
% 5.47/1.10  fof(f110,plain,(
% 5.47/1.10    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 5.47/1.10    inference(cnf_transformation,[],[f35])).
% 5.47/1.10  fof(f35,plain,(
% 5.47/1.10    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 5.47/1.10    inference(ennf_transformation,[],[f17])).
% 5.47/1.10  fof(f17,axiom,(
% 5.47/1.10    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 5.47/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 5.47/1.11  fof(f143,plain,(
% 5.47/1.11    v3_ordinal1(sK1) | ~spl10_4),
% 5.47/1.11    inference(avatar_component_clause,[],[f141])).
% 5.47/1.11  fof(f141,plain,(
% 5.47/1.11    spl10_4 <=> v3_ordinal1(sK1)),
% 5.47/1.11    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 5.47/1.11  fof(f133,plain,(
% 5.47/1.11    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl10_2),
% 5.47/1.11    inference(avatar_component_clause,[],[f131])).
% 5.47/1.11  fof(f131,plain,(
% 5.47/1.11    spl10_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 5.47/1.11    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 5.47/1.11  fof(f3303,plain,(
% 5.47/1.11    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl10_4),
% 5.47/1.11    inference(unit_resulting_resolution,[],[f143,f114])).
% 5.47/1.11  fof(f114,plain,(
% 5.47/1.11    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 5.47/1.11    inference(definition_unfolding,[],[f76,f75])).
% 5.47/1.13  fof(f76,plain,(
% 5.47/1.13    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f22])).
% 5.47/1.13  fof(f22,plain,(
% 5.47/1.13    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 5.47/1.13    inference(ennf_transformation,[],[f12])).
% 5.47/1.13  fof(f12,axiom,(
% 5.47/1.13    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 5.47/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 5.47/1.13  fof(f69,plain,(
% 5.47/1.13    v3_ordinal1(sK0)),
% 5.47/1.13    inference(cnf_transformation,[],[f41])).
% 5.47/1.13  fof(f41,plain,(
% 5.47/1.13    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 5.47/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 5.47/1.13  fof(f39,plain,(
% 5.47/1.13    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 5.47/1.13    introduced(choice_axiom,[])).
% 5.47/1.13  fof(f40,plain,(
% 5.47/1.13    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 5.47/1.13    introduced(choice_axiom,[])).
% 5.47/1.13  fof(f38,plain,(
% 5.47/1.13    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 5.47/1.13    inference(rectify,[],[f37])).
% 5.47/1.13  fof(f37,plain,(
% 5.47/1.13    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 5.47/1.13    inference(flattening,[],[f36])).
% 5.47/1.13  fof(f36,plain,(
% 5.47/1.13    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 5.47/1.13    inference(nnf_transformation,[],[f21])).
% 5.47/1.13  fof(f21,plain,(
% 5.47/1.13    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 5.47/1.13    inference(flattening,[],[f20])).
% 5.47/1.13  fof(f20,plain,(
% 5.47/1.13    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 5.47/1.13    inference(ennf_transformation,[],[f19])).
% 5.47/1.13  fof(f19,negated_conjecture,(
% 5.47/1.13    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 5.47/1.13    inference(negated_conjecture,[],[f18])).
% 5.47/1.13  fof(f18,conjecture,(
% 5.47/1.13    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 5.47/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 5.47/1.13  fof(f6353,plain,(
% 5.47/1.13    ~r2_hidden(sK9(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl10_1 | ~spl10_3 | ~spl10_4)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f143,f4071,f5378,f116])).
% 5.47/1.13  fof(f5378,plain,(
% 5.47/1.13    ~r1_ordinal1(sK9(sK0,sK1),sK1) | (~spl10_1 | ~spl10_3 | ~spl10_4)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f143,f4071,f4096,f93])).
% 5.47/1.13  fof(f4096,plain,(
% 5.47/1.13    ~r1_tarski(sK9(sK0,sK1),sK1) | (~spl10_1 | ~spl10_3)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f3626,f110])).
% 5.47/1.13  fof(f3626,plain,(
% 5.47/1.13    r2_hidden(sK1,sK9(sK0,sK1)) | (~spl10_1 | ~spl10_3)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f138,f3350])).
% 5.47/1.13  fof(f3350,plain,(
% 5.47/1.13    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK9(sK0,X7))) ) | ~spl10_1),
% 5.47/1.13    inference(superposition,[],[f124,f3296])).
% 5.47/1.13  fof(f124,plain,(
% 5.47/1.13    ( ! [X0,X5] : (r2_hidden(X5,sK9(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 5.47/1.13    inference(equality_resolution,[],[f101])).
% 5.47/1.13  fof(f101,plain,(
% 5.47/1.13    ( ! [X0,X5,X1] : (r2_hidden(X5,sK9(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 5.47/1.13    inference(cnf_transformation,[],[f66])).
% 5.47/1.13  fof(f4071,plain,(
% 5.47/1.13    v3_ordinal1(sK9(sK0,sK1)) | (~spl10_1 | ~spl10_3)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f69,f3624,f92])).
% 5.47/1.13  fof(f92,plain,(
% 5.47/1.13    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f31])).
% 5.47/1.13  fof(f31,plain,(
% 5.47/1.13    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 5.47/1.13    inference(flattening,[],[f30])).
% 5.47/1.13  fof(f30,plain,(
% 5.47/1.13    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 5.47/1.13    inference(ennf_transformation,[],[f10])).
% 5.47/1.13  fof(f10,axiom,(
% 5.47/1.13    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 5.47/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 5.47/1.13  fof(f3295,plain,(
% 5.47/1.13    spl10_8 | ~spl10_9 | ~spl10_13),
% 5.47/1.13    inference(avatar_contradiction_clause,[],[f3294])).
% 5.47/1.13  fof(f3294,plain,(
% 5.47/1.13    $false | (spl10_8 | ~spl10_9 | ~spl10_13)),
% 5.47/1.13    inference(subsumption_resolution,[],[f3293,f2702])).
% 5.47/1.13  fof(f2702,plain,(
% 5.47/1.13    r2_hidden(sK8(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl10_9),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f275,f118])).
% 5.47/1.13  fof(f118,plain,(
% 5.47/1.13    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 5.47/1.13    inference(definition_unfolding,[],[f108,f75])).
% 5.47/1.13  fof(f108,plain,(
% 5.47/1.13    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f68])).
% 5.47/1.13  fof(f68,plain,(
% 5.47/1.13    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 5.47/1.13    inference(flattening,[],[f67])).
% 5.47/1.13  fof(f67,plain,(
% 5.47/1.13    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 5.47/1.13    inference(nnf_transformation,[],[f9])).
% 5.47/1.13  fof(f9,axiom,(
% 5.47/1.13    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 5.47/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 5.47/1.13  fof(f275,plain,(
% 5.47/1.13    r2_hidden(sK8(sK0,sK0),sK0) | ~spl10_9),
% 5.47/1.13    inference(avatar_component_clause,[],[f273])).
% 5.47/1.13  fof(f273,plain,(
% 5.47/1.13    spl10_9 <=> r2_hidden(sK8(sK0,sK0),sK0)),
% 5.47/1.13    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 5.47/1.13  fof(f3293,plain,(
% 5.47/1.13    ~r2_hidden(sK8(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0))) | (spl10_8 | ~spl10_9 | ~spl10_13)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f69,f2698,f2982,f116])).
% 5.47/1.13  fof(f2982,plain,(
% 5.47/1.13    ~r1_ordinal1(sK8(sK0,sK0),sK0) | (spl10_8 | ~spl10_9 | ~spl10_13)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f69,f2698,f2828,f93])).
% 5.47/1.13  fof(f2828,plain,(
% 5.47/1.13    ~r1_tarski(sK8(sK0,sK0),sK0) | (spl10_8 | ~spl10_13)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f270,f453,f98])).
% 5.47/1.13  fof(f98,plain,(
% 5.47/1.13    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f60])).
% 5.47/1.13  fof(f60,plain,(
% 5.47/1.13    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 5.47/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).
% 5.47/1.13  fof(f59,plain,(
% 5.47/1.13    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 5.47/1.13    introduced(choice_axiom,[])).
% 5.47/1.13  fof(f58,plain,(
% 5.47/1.13    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 5.47/1.13    inference(rectify,[],[f57])).
% 5.47/1.13  fof(f57,plain,(
% 5.47/1.13    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 5.47/1.13    inference(nnf_transformation,[],[f34])).
% 5.47/1.13  fof(f34,plain,(
% 5.47/1.13    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 5.47/1.13    inference(ennf_transformation,[],[f1])).
% 5.47/1.13  fof(f1,axiom,(
% 5.47/1.13    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.47/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 5.47/1.13  fof(f453,plain,(
% 5.47/1.13    r2_hidden(sK7(sK0,sK0),sK8(sK0,sK0)) | ~spl10_13),
% 5.47/1.13    inference(avatar_component_clause,[],[f451])).
% 5.47/1.13  fof(f451,plain,(
% 5.47/1.13    spl10_13 <=> r2_hidden(sK7(sK0,sK0),sK8(sK0,sK0))),
% 5.47/1.13    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 5.47/1.13  fof(f270,plain,(
% 5.47/1.13    ~r2_hidden(sK7(sK0,sK0),sK0) | spl10_8),
% 5.47/1.13    inference(avatar_component_clause,[],[f269])).
% 5.47/1.13  fof(f269,plain,(
% 5.47/1.13    spl10_8 <=> r2_hidden(sK7(sK0,sK0),sK0)),
% 5.47/1.13    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 5.47/1.13  fof(f2698,plain,(
% 5.47/1.13    v3_ordinal1(sK8(sK0,sK0)) | ~spl10_9),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f69,f275,f92])).
% 5.47/1.13  fof(f454,plain,(
% 5.47/1.13    spl10_8 | spl10_13 | spl10_1),
% 5.47/1.13    inference(avatar_split_clause,[],[f304,f127,f451,f269])).
% 5.47/1.13  fof(f304,plain,(
% 5.47/1.13    r2_hidden(sK7(sK0,sK0),sK8(sK0,sK0)) | r2_hidden(sK7(sK0,sK0),sK0) | spl10_1),
% 5.47/1.13    inference(equality_resolution,[],[f166])).
% 5.47/1.13  fof(f166,plain,(
% 5.47/1.13    ( ! [X0] : (sK0 != X0 | r2_hidden(sK7(sK0,X0),sK8(sK0,X0)) | r2_hidden(sK7(sK0,X0),X0)) ) | spl10_1),
% 5.47/1.13    inference(superposition,[],[f162,f104])).
% 5.47/1.13  fof(f104,plain,(
% 5.47/1.13    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(sK7(X0,X1),X1)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f66])).
% 5.47/1.13  fof(f162,plain,(
% 5.47/1.13    sK0 != k3_tarski(sK0) | spl10_1),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f129,f83])).
% 5.47/1.13  fof(f83,plain,(
% 5.47/1.13    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 5.47/1.13    inference(cnf_transformation,[],[f45])).
% 5.47/1.13  fof(f129,plain,(
% 5.47/1.13    ~v4_ordinal1(sK0) | spl10_1),
% 5.47/1.13    inference(avatar_component_clause,[],[f127])).
% 5.47/1.13  fof(f445,plain,(
% 5.47/1.13    spl10_1 | ~spl10_5 | ~spl10_8),
% 5.47/1.13    inference(avatar_contradiction_clause,[],[f444])).
% 5.47/1.13  fof(f444,plain,(
% 5.47/1.13    $false | (spl10_1 | ~spl10_5 | ~spl10_8)),
% 5.47/1.13    inference(subsumption_resolution,[],[f443,f290])).
% 5.47/1.13  fof(f290,plain,(
% 5.47/1.13    ~r2_hidden(k2_xboole_0(sK7(sK0,sK0),k1_tarski(sK7(sK0,sK0))),sK0) | (spl10_1 | ~spl10_8)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f162,f113,f271,f106])).
% 5.47/1.13  fof(f106,plain,(
% 5.47/1.13    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK7(X0,X1),X3) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f66])).
% 5.47/1.13  fof(f271,plain,(
% 5.47/1.13    r2_hidden(sK7(sK0,sK0),sK0) | ~spl10_8),
% 5.47/1.13    inference(avatar_component_clause,[],[f269])).
% 5.47/1.13  fof(f113,plain,(
% 5.47/1.13    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 5.47/1.13    inference(definition_unfolding,[],[f74,f75])).
% 5.47/1.13  fof(f74,plain,(
% 5.47/1.13    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 5.47/1.13    inference(cnf_transformation,[],[f8])).
% 5.47/1.13  fof(f8,axiom,(
% 5.47/1.13    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 5.47/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 5.47/1.13  fof(f443,plain,(
% 5.47/1.13    r2_hidden(k2_xboole_0(sK7(sK0,sK0),k1_tarski(sK7(sK0,sK0))),sK0) | (~spl10_5 | ~spl10_8)),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f271,f291,f147])).
% 5.47/1.13  fof(f147,plain,(
% 5.47/1.13    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl10_5),
% 5.47/1.13    inference(avatar_component_clause,[],[f146])).
% 5.47/1.13  fof(f146,plain,(
% 5.47/1.13    spl10_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 5.47/1.13    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 5.47/1.13  fof(f291,plain,(
% 5.47/1.13    v3_ordinal1(sK7(sK0,sK0)) | ~spl10_8),
% 5.47/1.13    inference(unit_resulting_resolution,[],[f69,f271,f92])).
% 5.47/1.13  fof(f276,plain,(
% 5.47/1.13    spl10_8 | spl10_9 | spl10_1),
% 5.47/1.13    inference(avatar_split_clause,[],[f267,f127,f273,f269])).
% 5.47/1.13  fof(f267,plain,(
% 5.47/1.13    r2_hidden(sK8(sK0,sK0),sK0) | r2_hidden(sK7(sK0,sK0),sK0) | spl10_1),
% 5.47/1.13    inference(equality_resolution,[],[f167])).
% 5.47/1.13  fof(f167,plain,(
% 5.47/1.13    ( ! [X1] : (sK0 != X1 | r2_hidden(sK8(sK0,X1),sK0) | r2_hidden(sK7(sK0,X1),X1)) ) | spl10_1),
% 5.47/1.13    inference(superposition,[],[f162,f105])).
% 5.47/1.13  fof(f105,plain,(
% 5.47/1.13    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK8(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f66])).
% 5.47/1.13  fof(f148,plain,(
% 5.47/1.13    spl10_1 | spl10_5),
% 5.47/1.13    inference(avatar_split_clause,[],[f112,f146,f127])).
% 5.47/1.13  fof(f112,plain,(
% 5.47/1.13    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 5.47/1.13    inference(definition_unfolding,[],[f70,f75])).
% 5.47/1.13  fof(f70,plain,(
% 5.47/1.13    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 5.47/1.13    inference(cnf_transformation,[],[f41])).
% 5.47/1.13  fof(f144,plain,(
% 5.47/1.13    ~spl10_1 | spl10_4),
% 5.47/1.13    inference(avatar_split_clause,[],[f71,f141,f127])).
% 5.47/1.13  fof(f71,plain,(
% 5.47/1.13    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 5.47/1.13    inference(cnf_transformation,[],[f41])).
% 5.47/1.13  fof(f139,plain,(
% 5.47/1.13    ~spl10_1 | spl10_3),
% 5.47/1.13    inference(avatar_split_clause,[],[f72,f136,f127])).
% 5.47/1.13  fof(f72,plain,(
% 5.47/1.13    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 5.47/1.13    inference(cnf_transformation,[],[f41])).
% 5.47/1.13  fof(f134,plain,(
% 5.47/1.13    ~spl10_1 | ~spl10_2),
% 5.47/1.13    inference(avatar_split_clause,[],[f111,f131,f127])).
% 5.47/1.13  fof(f111,plain,(
% 5.47/1.13    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 5.47/1.13    inference(definition_unfolding,[],[f73,f75])).
% 5.47/1.13  fof(f73,plain,(
% 5.47/1.13    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 5.47/1.13    inference(cnf_transformation,[],[f41])).
% 5.47/1.13  % SZS output end Proof for theBenchmark
% 5.47/1.13  % (27344)------------------------------
% 5.47/1.13  % (27344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.47/1.13  % (27344)Termination reason: Refutation
% 5.47/1.13  
% 5.47/1.13  % (27344)Memory used [KB]: 14072
% 5.47/1.13  % (27344)Time elapsed: 0.676 s
% 5.47/1.13  % (27344)------------------------------
% 5.47/1.13  % (27344)------------------------------
% 5.47/1.13  % (27359)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.47/1.13  % (27316)Success in time 0.766 s
%------------------------------------------------------------------------------
