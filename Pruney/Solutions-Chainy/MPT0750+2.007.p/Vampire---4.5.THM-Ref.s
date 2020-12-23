%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:40 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
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
fof(f2211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f130,f135,f139,f206,f326,f667,f712,f2210])).

fof(f2210,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f2209])).

fof(f2209,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f2208,f807])).

fof(f807,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f129,f747])).

fof(f747,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f114,f718])).

fof(f718,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f119,f77])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f119,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f114,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).

fof(f57,plain,(
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

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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

fof(f129,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f2208,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f2207,f1017])).

fof(f1017,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f63,f212,f124,f779,f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f779,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f63,f134,f735,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f70,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f735,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f63,f134,f726,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f726,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f129,f100])).

fof(f100,plain,(
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

fof(f134,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f124,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f212,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f134,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f71,f70])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f63,plain,(
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

fof(f2207,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f134,f987,f1605,f107])).

fof(f1605,plain,
    ( ~ r1_ordinal1(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f134,f987,f1000,f83])).

fof(f1000,plain,
    ( ~ r1_tarski(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f811,f100])).

fof(f811,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f129,f748])).

fof(f748,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f115,f718])).

fof(f115,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f987,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f63,f807,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f712,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f710,f673])).

fof(f673,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f231,f104,f201,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f201,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f104,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f69,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f231,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f120,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f710,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f201,f674,f138])).

fof(f138,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f674,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f63,f201,f81])).

fof(f667,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f656,f501])).

fof(f501,plain,
    ( ~ r1_ordinal1(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f63,f279,f386,f83])).

fof(f386,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f325,f200,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
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

fof(f200,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f325,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f279,plain,
    ( v3_ordinal1(sK6(sK0,sK0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f63,f205,f81])).

fof(f205,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f656,plain,
    ( r1_ordinal1(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f63,f279,f284,f107])).

fof(f284,plain,
    ( r2_hidden(sK6(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f205,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f98,f70])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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

fof(f326,plain,
    ( spl8_6
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f321,f118,f323,f199])).

fof(f321,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f244])).

fof(f244,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f231,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f206,plain,
    ( spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f197,f118,f203,f199])).

fof(f197,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f155])).

fof(f155,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK6(sK0,X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f150,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f150,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f120,f78])).

fof(f139,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f102,f137,f118])).

fof(f102,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f64,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f135,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f65,f132,f118])).

fof(f65,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f130,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f66,f127,f118])).

fof(f66,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f101,f122,f118])).

fof(f101,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f67,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (23761)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (23777)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (23775)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (23767)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (23775)Refutation not found, incomplete strategy% (23775)------------------------------
% 0.21/0.51  % (23775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23775)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23775)Memory used [KB]: 10746
% 0.21/0.51  % (23775)Time elapsed: 0.060 s
% 0.21/0.51  % (23775)------------------------------
% 0.21/0.51  % (23775)------------------------------
% 0.21/0.52  % (23759)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (23763)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  % (23756)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (23758)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (23757)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.54  % (23771)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.54  % (23778)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (23755)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (23754)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (23755)Refutation not found, incomplete strategy% (23755)------------------------------
% 1.30/0.54  % (23755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (23755)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (23755)Memory used [KB]: 10746
% 1.30/0.54  % (23755)Time elapsed: 0.127 s
% 1.30/0.54  % (23755)------------------------------
% 1.30/0.54  % (23755)------------------------------
% 1.30/0.54  % (23780)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.54  % (23779)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (23782)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.54  % (23781)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (23770)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.55  % (23772)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.55  % (23766)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.55  % (23773)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (23773)Refutation not found, incomplete strategy% (23773)------------------------------
% 1.47/0.55  % (23773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (23773)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (23773)Memory used [KB]: 10746
% 1.47/0.55  % (23773)Time elapsed: 0.148 s
% 1.47/0.55  % (23773)------------------------------
% 1.47/0.55  % (23773)------------------------------
% 1.47/0.55  % (23762)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  % (23764)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.56  % (23765)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  % (23774)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.56  % (23774)Refutation not found, incomplete strategy% (23774)------------------------------
% 1.47/0.56  % (23774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (23774)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (23774)Memory used [KB]: 1663
% 1.47/0.56  % (23774)Time elapsed: 0.148 s
% 1.47/0.56  % (23774)------------------------------
% 1.47/0.56  % (23774)------------------------------
% 1.47/0.57  % (23753)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.58  % (23776)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.58  % (23769)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.58  % (23768)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.59  % (23760)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.99/0.65  % (23801)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.99/0.65  % (23800)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.40/0.69  % (23802)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.40/0.70  % (23803)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.40/0.74  % (23779)Refutation found. Thanks to Tanya!
% 2.40/0.74  % SZS status Theorem for theBenchmark
% 2.40/0.74  % SZS output start Proof for theBenchmark
% 2.40/0.74  fof(f2211,plain,(
% 2.40/0.74    $false),
% 2.40/0.74    inference(avatar_sat_refutation,[],[f125,f130,f135,f139,f206,f326,f667,f712,f2210])).
% 2.40/0.74  fof(f2210,plain,(
% 2.40/0.74    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 2.40/0.74    inference(avatar_contradiction_clause,[],[f2209])).
% 2.40/0.74  fof(f2209,plain,(
% 2.40/0.74    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(subsumption_resolution,[],[f2208,f807])).
% 2.40/0.74  fof(f807,plain,(
% 2.40/0.74    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f129,f747])).
% 2.40/0.74  fof(f747,plain,(
% 2.40/0.74    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 2.40/0.74    inference(superposition,[],[f114,f718])).
% 2.40/0.74  fof(f718,plain,(
% 2.40/0.74    sK0 = k3_tarski(sK0) | ~spl8_1),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f119,f77])).
% 2.40/0.74  fof(f77,plain,(
% 2.40/0.74    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f45])).
% 2.40/0.74  fof(f45,plain,(
% 2.40/0.74    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 2.40/0.74    inference(nnf_transformation,[],[f6])).
% 2.40/0.74  fof(f6,axiom,(
% 2.40/0.74    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 2.40/0.74  fof(f119,plain,(
% 2.40/0.74    v4_ordinal1(sK0) | ~spl8_1),
% 2.40/0.74    inference(avatar_component_clause,[],[f118])).
% 2.40/0.74  fof(f118,plain,(
% 2.40/0.74    spl8_1 <=> v4_ordinal1(sK0)),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.40/0.74  fof(f114,plain,(
% 2.40/0.74    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.40/0.74    inference(equality_resolution,[],[f92])).
% 2.40/0.74  fof(f92,plain,(
% 2.40/0.74    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.40/0.74    inference(cnf_transformation,[],[f60])).
% 2.40/0.74  fof(f60,plain,(
% 2.40/0.74    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).
% 2.40/0.74  fof(f57,plain,(
% 2.40/0.74    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f58,plain,(
% 2.40/0.74    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f59,plain,(
% 2.40/0.74    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f56,plain,(
% 2.40/0.74    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.40/0.74    inference(rectify,[],[f55])).
% 2.40/0.74  fof(f55,plain,(
% 2.40/0.74    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.40/0.74    inference(nnf_transformation,[],[f3])).
% 2.40/0.74  fof(f3,axiom,(
% 2.40/0.74    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.40/0.74  fof(f129,plain,(
% 2.40/0.74    r2_hidden(sK1,sK0) | ~spl8_3),
% 2.40/0.74    inference(avatar_component_clause,[],[f127])).
% 2.40/0.74  fof(f127,plain,(
% 2.40/0.74    spl8_3 <=> r2_hidden(sK1,sK0)),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.40/0.74  fof(f2208,plain,(
% 2.40/0.74    ~r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(forward_demodulation,[],[f2207,f1017])).
% 2.40/0.74  fof(f1017,plain,(
% 2.40/0.74    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f212,f124,f779,f74])).
% 2.40/0.74  fof(f74,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f25])).
% 2.40/0.74  fof(f25,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(flattening,[],[f24])).
% 2.40/0.74  fof(f24,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f12])).
% 2.40/0.74  fof(f12,axiom,(
% 2.40/0.74    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 2.40/0.74  fof(f779,plain,(
% 2.40/0.74    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f134,f735,f107])).
% 2.40/0.74  fof(f107,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.40/0.74    inference(definition_unfolding,[],[f72,f70])).
% 2.40/0.74  fof(f70,plain,(
% 2.40/0.74    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.40/0.74    inference(cnf_transformation,[],[f5])).
% 2.40/0.74  fof(f5,axiom,(
% 2.40/0.74    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.40/0.74  fof(f72,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f42])).
% 2.40/0.74  fof(f42,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(nnf_transformation,[],[f23])).
% 2.40/0.74  fof(f23,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f14])).
% 2.40/0.74  fof(f14,axiom,(
% 2.40/0.74    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 2.40/0.74  fof(f735,plain,(
% 2.40/0.74    ~r1_ordinal1(sK0,sK1) | (~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f134,f726,f83])).
% 2.40/0.74  fof(f83,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f48])).
% 2.40/0.74  fof(f48,plain,(
% 2.40/0.74    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(nnf_transformation,[],[f33])).
% 2.40/0.74  fof(f33,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(flattening,[],[f32])).
% 2.40/0.74  fof(f32,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.40/0.74    inference(ennf_transformation,[],[f7])).
% 2.40/0.74  fof(f7,axiom,(
% 2.40/0.74    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 2.40/0.74  fof(f726,plain,(
% 2.40/0.74    ~r1_tarski(sK0,sK1) | ~spl8_3),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f129,f100])).
% 2.40/0.74  fof(f100,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f35])).
% 2.40/0.74  fof(f35,plain,(
% 2.40/0.74    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.40/0.74    inference(ennf_transformation,[],[f17])).
% 2.40/0.74  fof(f17,axiom,(
% 2.40/0.74    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.40/0.74  fof(f134,plain,(
% 2.40/0.74    v3_ordinal1(sK1) | ~spl8_4),
% 2.40/0.74    inference(avatar_component_clause,[],[f132])).
% 2.40/0.74  fof(f132,plain,(
% 2.40/0.74    spl8_4 <=> v3_ordinal1(sK1)),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.40/0.74  fof(f124,plain,(
% 2.40/0.74    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 2.40/0.74    inference(avatar_component_clause,[],[f122])).
% 2.40/0.74  fof(f122,plain,(
% 2.40/0.74    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.40/0.74  fof(f212,plain,(
% 2.40/0.74    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f134,f105])).
% 2.40/0.74  fof(f105,plain,(
% 2.40/0.74    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.40/0.74    inference(definition_unfolding,[],[f71,f70])).
% 2.40/0.74  fof(f71,plain,(
% 2.40/0.74    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f22])).
% 2.40/0.74  fof(f22,plain,(
% 2.40/0.74    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f13])).
% 2.40/0.74  fof(f13,axiom,(
% 2.40/0.74    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 2.40/0.74  fof(f63,plain,(
% 2.40/0.74    v3_ordinal1(sK0)),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  fof(f41,plain,(
% 2.40/0.74    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 2.40/0.74  fof(f39,plain,(
% 2.40/0.74    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f40,plain,(
% 2.40/0.74    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f38,plain,(
% 2.40/0.74    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.40/0.74    inference(rectify,[],[f37])).
% 2.40/0.74  fof(f37,plain,(
% 2.40/0.74    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.40/0.74    inference(flattening,[],[f36])).
% 2.40/0.74  fof(f36,plain,(
% 2.40/0.74    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.40/0.74    inference(nnf_transformation,[],[f21])).
% 2.40/0.74  fof(f21,plain,(
% 2.40/0.74    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.40/0.74    inference(flattening,[],[f20])).
% 2.40/0.74  fof(f20,plain,(
% 2.40/0.74    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f19])).
% 2.40/0.74  fof(f19,negated_conjecture,(
% 2.40/0.74    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.40/0.74    inference(negated_conjecture,[],[f18])).
% 2.40/0.74  fof(f18,conjecture,(
% 2.40/0.74    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 2.40/0.74  fof(f2207,plain,(
% 2.40/0.74    ~r2_hidden(sK7(sK0,sK1),k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f134,f987,f1605,f107])).
% 2.40/0.74  fof(f1605,plain,(
% 2.40/0.74    ~r1_ordinal1(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f134,f987,f1000,f83])).
% 2.40/0.74  fof(f1000,plain,(
% 2.40/0.74    ~r1_tarski(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f811,f100])).
% 2.40/0.74  fof(f811,plain,(
% 2.40/0.74    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f129,f748])).
% 2.40/0.74  fof(f748,plain,(
% 2.40/0.74    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 2.40/0.74    inference(superposition,[],[f115,f718])).
% 2.40/0.74  fof(f115,plain,(
% 2.40/0.74    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.40/0.74    inference(equality_resolution,[],[f91])).
% 2.40/0.74  fof(f91,plain,(
% 2.40/0.74    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.40/0.74    inference(cnf_transformation,[],[f60])).
% 2.40/0.74  fof(f987,plain,(
% 2.40/0.74    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f807,f81])).
% 2.40/0.74  fof(f81,plain,(
% 2.40/0.74    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f29])).
% 2.40/0.74  fof(f29,plain,(
% 2.40/0.74    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.40/0.74    inference(flattening,[],[f28])).
% 2.40/0.74  fof(f28,plain,(
% 2.40/0.74    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.40/0.74    inference(ennf_transformation,[],[f11])).
% 2.40/0.74  fof(f11,axiom,(
% 2.40/0.74    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 2.40/0.74  fof(f712,plain,(
% 2.40/0.74    spl8_1 | ~spl8_5 | ~spl8_6),
% 2.40/0.74    inference(avatar_contradiction_clause,[],[f711])).
% 2.40/0.74  fof(f711,plain,(
% 2.40/0.74    $false | (spl8_1 | ~spl8_5 | ~spl8_6)),
% 2.40/0.74    inference(subsumption_resolution,[],[f710,f673])).
% 2.40/0.74  fof(f673,plain,(
% 2.40/0.74    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_6)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f231,f104,f201,f96])).
% 2.40/0.74  fof(f96,plain,(
% 2.40/0.74    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f60])).
% 2.40/0.74  fof(f201,plain,(
% 2.40/0.74    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_6),
% 2.40/0.74    inference(avatar_component_clause,[],[f199])).
% 2.40/0.74  fof(f199,plain,(
% 2.40/0.74    spl8_6 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.40/0.74  fof(f104,plain,(
% 2.40/0.74    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.40/0.74    inference(definition_unfolding,[],[f69,f70])).
% 2.40/0.74  fof(f69,plain,(
% 2.40/0.74    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.40/0.74    inference(cnf_transformation,[],[f8])).
% 2.40/0.74  fof(f8,axiom,(
% 2.40/0.74    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.40/0.74  fof(f231,plain,(
% 2.40/0.74    sK0 != k3_tarski(sK0) | spl8_1),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f120,f78])).
% 2.40/0.74  fof(f78,plain,(
% 2.40/0.74    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 2.40/0.74    inference(cnf_transformation,[],[f45])).
% 2.40/0.74  fof(f120,plain,(
% 2.40/0.74    ~v4_ordinal1(sK0) | spl8_1),
% 2.40/0.74    inference(avatar_component_clause,[],[f118])).
% 2.40/0.74  fof(f710,plain,(
% 2.40/0.74    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_6)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f201,f674,f138])).
% 2.40/0.74  fof(f138,plain,(
% 2.40/0.74    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 2.40/0.74    inference(avatar_component_clause,[],[f137])).
% 2.40/0.74  fof(f137,plain,(
% 2.40/0.74    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.40/0.74  fof(f674,plain,(
% 2.40/0.74    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_6),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f201,f81])).
% 2.40/0.74  fof(f667,plain,(
% 2.40/0.74    spl8_6 | ~spl8_7 | ~spl8_8),
% 2.40/0.74    inference(avatar_contradiction_clause,[],[f666])).
% 2.40/0.74  fof(f666,plain,(
% 2.40/0.74    $false | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 2.40/0.74    inference(subsumption_resolution,[],[f656,f501])).
% 2.40/0.74  fof(f501,plain,(
% 2.40/0.74    ~r1_ordinal1(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f279,f386,f83])).
% 2.40/0.74  fof(f386,plain,(
% 2.40/0.74    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_8)),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f325,f200,f88])).
% 2.40/0.74  fof(f88,plain,(
% 2.40/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f54])).
% 2.40/0.74  fof(f54,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).
% 2.40/0.74  fof(f53,plain,(
% 2.40/0.74    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f52,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.74    inference(rectify,[],[f51])).
% 2.40/0.74  fof(f51,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.74    inference(nnf_transformation,[],[f34])).
% 2.40/0.74  fof(f34,plain,(
% 2.40/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.74    inference(ennf_transformation,[],[f1])).
% 2.40/0.74  fof(f1,axiom,(
% 2.40/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.74  fof(f200,plain,(
% 2.40/0.74    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_6),
% 2.40/0.74    inference(avatar_component_clause,[],[f199])).
% 2.40/0.74  fof(f325,plain,(
% 2.40/0.74    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_8),
% 2.40/0.74    inference(avatar_component_clause,[],[f323])).
% 2.40/0.74  fof(f323,plain,(
% 2.40/0.74    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.40/0.74  fof(f279,plain,(
% 2.40/0.74    v3_ordinal1(sK6(sK0,sK0)) | ~spl8_7),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f205,f81])).
% 2.40/0.74  fof(f205,plain,(
% 2.40/0.74    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_7),
% 2.40/0.74    inference(avatar_component_clause,[],[f203])).
% 2.40/0.74  fof(f203,plain,(
% 2.40/0.74    spl8_7 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 2.40/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.40/0.74  fof(f656,plain,(
% 2.40/0.74    r1_ordinal1(sK6(sK0,sK0),sK0) | ~spl8_7),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f63,f279,f284,f107])).
% 2.40/0.74  fof(f284,plain,(
% 2.40/0.74    r2_hidden(sK6(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl8_7),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f205,f109])).
% 2.40/0.74  fof(f109,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 2.40/0.74    inference(definition_unfolding,[],[f98,f70])).
% 2.40/0.74  fof(f98,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f62])).
% 2.40/0.74  fof(f62,plain,(
% 2.40/0.74    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.40/0.74    inference(flattening,[],[f61])).
% 2.40/0.74  fof(f61,plain,(
% 2.40/0.74    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.40/0.74    inference(nnf_transformation,[],[f9])).
% 2.40/0.74  fof(f9,axiom,(
% 2.40/0.74    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 2.40/0.74  fof(f326,plain,(
% 2.40/0.74    spl8_6 | spl8_8 | spl8_1),
% 2.40/0.74    inference(avatar_split_clause,[],[f321,f118,f323,f199])).
% 2.40/0.74  fof(f321,plain,(
% 2.40/0.74    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 2.40/0.74    inference(equality_resolution,[],[f244])).
% 2.40/0.74  fof(f244,plain,(
% 2.40/0.74    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 2.40/0.74    inference(superposition,[],[f231,f94])).
% 2.40/0.74  fof(f94,plain,(
% 2.40/0.74    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f60])).
% 2.40/0.74  fof(f206,plain,(
% 2.40/0.74    spl8_6 | spl8_7 | spl8_1),
% 2.40/0.74    inference(avatar_split_clause,[],[f197,f118,f203,f199])).
% 2.40/0.74  fof(f197,plain,(
% 2.40/0.74    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 2.40/0.74    inference(equality_resolution,[],[f155])).
% 2.40/0.74  fof(f155,plain,(
% 2.40/0.74    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 2.40/0.74    inference(superposition,[],[f150,f95])).
% 2.40/0.74  fof(f95,plain,(
% 2.40/0.74    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f60])).
% 2.40/0.74  fof(f150,plain,(
% 2.40/0.74    sK0 != k3_tarski(sK0) | spl8_1),
% 2.40/0.74    inference(unit_resulting_resolution,[],[f120,f78])).
% 2.40/0.74  fof(f139,plain,(
% 2.40/0.74    spl8_1 | spl8_5),
% 2.40/0.74    inference(avatar_split_clause,[],[f102,f137,f118])).
% 2.40/0.74  fof(f102,plain,(
% 2.40/0.74    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.40/0.74    inference(definition_unfolding,[],[f64,f70])).
% 2.40/0.74  fof(f64,plain,(
% 2.40/0.74    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  fof(f135,plain,(
% 2.40/0.74    ~spl8_1 | spl8_4),
% 2.40/0.74    inference(avatar_split_clause,[],[f65,f132,f118])).
% 2.40/0.74  fof(f65,plain,(
% 2.40/0.74    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  fof(f130,plain,(
% 2.40/0.74    ~spl8_1 | spl8_3),
% 2.40/0.74    inference(avatar_split_clause,[],[f66,f127,f118])).
% 2.40/0.74  fof(f66,plain,(
% 2.40/0.74    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  fof(f125,plain,(
% 2.40/0.74    ~spl8_1 | ~spl8_2),
% 2.40/0.74    inference(avatar_split_clause,[],[f101,f122,f118])).
% 2.40/0.74  fof(f101,plain,(
% 2.40/0.74    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 2.40/0.74    inference(definition_unfolding,[],[f67,f70])).
% 2.40/0.74  fof(f67,plain,(
% 2.40/0.74    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  % SZS output end Proof for theBenchmark
% 2.40/0.74  % (23779)------------------------------
% 2.40/0.74  % (23779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.74  % (23779)Termination reason: Refutation
% 2.40/0.74  
% 2.40/0.74  % (23779)Memory used [KB]: 12281
% 2.40/0.74  % (23779)Time elapsed: 0.320 s
% 2.40/0.74  % (23779)------------------------------
% 2.40/0.74  % (23779)------------------------------
% 2.40/0.74  % (23750)Success in time 0.381 s
%------------------------------------------------------------------------------
