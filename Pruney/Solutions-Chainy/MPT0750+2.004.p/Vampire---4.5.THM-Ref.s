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

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 402 expanded)
%              Number of leaves         :   29 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          :  518 (2032 expanded)
%              Number of equality atoms :   29 ( 110 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1525,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f212,f353,f435,f509,f1524])).

fof(f1524,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f1523])).

fof(f1523,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1521,f957])).

fof(f957,plain,
    ( r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f952,f797])).

fof(f797,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f68,f219,f126,f571,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f571,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f68,f136,f527,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f79,f74])).

fof(f74,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f527,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f68,f136,f520,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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

fof(f520,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f131,f105])).

fof(f105,plain,(
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

fof(f131,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

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

fof(f219,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f136,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f75,f74])).

fof(f75,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f68,plain,(
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

fof(f952,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f136,f610,f773,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f77,f74])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f773,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f68,f606,f89])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f606,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f131,f540])).

fof(f540,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f117,f510])).

fof(f510,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f121,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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

fof(f121,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f117,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f63,f66,f65,f64])).

fof(f64,plain,(
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

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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

fof(f610,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f131,f541])).

fof(f541,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f118,f510])).

fof(f118,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1521,plain,
    ( ~ r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f68,f773,f778,f91])).

fof(f778,plain,
    ( ~ r1_tarski(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f606,f105])).

fof(f509,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f507,f441])).

fof(f441,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f237,f108,f207,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f207,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f73,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f237,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f122,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f507,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f207,f443,f140])).

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

fof(f443,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f68,f207,f89])).

fof(f435,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f429,f299])).

fof(f299,plain,
    ( r1_tarski(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f142,f211,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f211,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f142,plain,(
    v1_ordinal1(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f76])).

fof(f76,plain,(
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

fof(f429,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f206,f352,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
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

fof(f352,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f206,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f353,plain,
    ( spl8_6
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f348,f120,f350,f205])).

fof(f348,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f249])).

fof(f249,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f237,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f212,plain,
    ( spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f203,f120,f209,f205])).

fof(f203,plain,
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
    inference(superposition,[],[f152,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f152,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f122,f85])).

fof(f141,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f107,f139,f120])).

fof(f107,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f69,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f70,f134,f120])).

fof(f70,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f71,f129,f120])).

fof(f71,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f106,f124,f120])).

fof(f106,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f72,f74])).

fof(f72,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (22679)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (22694)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (22686)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (22695)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (22694)Refutation not found, incomplete strategy% (22694)------------------------------
% 0.20/0.50  % (22694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22678)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (22694)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22694)Memory used [KB]: 10746
% 0.20/0.51  % (22694)Time elapsed: 0.066 s
% 0.20/0.51  % (22694)------------------------------
% 0.20/0.51  % (22694)------------------------------
% 0.20/0.51  % (22687)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (22681)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (22674)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (22676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (22675)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (22680)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (22692)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (22684)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (22673)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (22677)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (22700)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (22698)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (22672)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (22699)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (22701)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (22690)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (22689)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (22693)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (22692)Refutation not found, incomplete strategy% (22692)------------------------------
% 0.20/0.54  % (22692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22692)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22692)Memory used [KB]: 10746
% 0.20/0.54  % (22692)Time elapsed: 0.152 s
% 0.20/0.54  % (22692)------------------------------
% 0.20/0.54  % (22692)------------------------------
% 0.20/0.54  % (22693)Refutation not found, incomplete strategy% (22693)------------------------------
% 0.20/0.54  % (22693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22693)Memory used [KB]: 1663
% 0.20/0.54  % (22693)Time elapsed: 0.149 s
% 0.20/0.54  % (22693)------------------------------
% 0.20/0.54  % (22693)------------------------------
% 0.20/0.54  % (22696)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (22691)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (22685)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (22682)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (22697)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (22688)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (22683)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.62  % (22702)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.67  % (22698)Refutation found. Thanks to Tanya!
% 0.20/0.67  % SZS status Theorem for theBenchmark
% 0.20/0.67  % SZS output start Proof for theBenchmark
% 0.20/0.67  fof(f1525,plain,(
% 0.20/0.67    $false),
% 0.20/0.67    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f212,f353,f435,f509,f1524])).
% 0.20/0.67  fof(f1524,plain,(
% 0.20/0.67    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 0.20/0.67    inference(avatar_contradiction_clause,[],[f1523])).
% 0.20/0.67  fof(f1523,plain,(
% 0.20/0.67    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.67    inference(subsumption_resolution,[],[f1521,f957])).
% 0.20/0.67  fof(f957,plain,(
% 0.20/0.67    r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.67    inference(forward_demodulation,[],[f952,f797])).
% 0.20/0.67  fof(f797,plain,(
% 0.20/0.67    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f219,f126,f571,f81])).
% 0.20/0.67  fof(f81,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f30])).
% 0.20/0.67  fof(f30,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(flattening,[],[f29])).
% 0.20/0.67  fof(f29,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f12])).
% 0.20/0.67  fof(f12,axiom,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.67  fof(f571,plain,(
% 0.20/0.67    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_3 | ~spl8_4)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f136,f527,f113])).
% 0.20/0.67  fof(f113,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(definition_unfolding,[],[f79,f74])).
% 0.20/0.67  fof(f74,plain,(
% 0.20/0.67    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.67    inference(cnf_transformation,[],[f6])).
% 0.20/0.67  fof(f6,axiom,(
% 0.20/0.67    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.67  fof(f79,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f49])).
% 0.20/0.67  fof(f49,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(nnf_transformation,[],[f28])).
% 0.20/0.67  fof(f28,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f15])).
% 0.20/0.67  fof(f15,axiom,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.67  fof(f527,plain,(
% 0.20/0.67    ~r1_ordinal1(sK0,sK1) | (~spl8_3 | ~spl8_4)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f136,f520,f91])).
% 0.20/0.67  fof(f91,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f55])).
% 0.20/0.67  fof(f55,plain,(
% 0.20/0.67    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(nnf_transformation,[],[f39])).
% 0.20/0.67  fof(f39,plain,(
% 0.20/0.67    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(flattening,[],[f38])).
% 0.20/0.67  fof(f38,plain,(
% 0.20/0.67    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.67    inference(ennf_transformation,[],[f9])).
% 0.20/0.67  fof(f9,axiom,(
% 0.20/0.67    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.67  fof(f520,plain,(
% 0.20/0.67    ~r1_tarski(sK0,sK1) | ~spl8_3),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f131,f105])).
% 0.20/0.67  fof(f105,plain,(
% 0.20/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f41])).
% 0.20/0.67  fof(f41,plain,(
% 0.20/0.67    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.67    inference(ennf_transformation,[],[f18])).
% 0.20/0.67  fof(f18,axiom,(
% 0.20/0.67    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.67  fof(f131,plain,(
% 0.20/0.67    r2_hidden(sK1,sK0) | ~spl8_3),
% 0.20/0.67    inference(avatar_component_clause,[],[f129])).
% 0.20/0.67  fof(f129,plain,(
% 0.20/0.67    spl8_3 <=> r2_hidden(sK1,sK0)),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.67  fof(f136,plain,(
% 0.20/0.67    v3_ordinal1(sK1) | ~spl8_4),
% 0.20/0.67    inference(avatar_component_clause,[],[f134])).
% 0.20/0.67  fof(f134,plain,(
% 0.20/0.67    spl8_4 <=> v3_ordinal1(sK1)),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.67  fof(f126,plain,(
% 0.20/0.67    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 0.20/0.67    inference(avatar_component_clause,[],[f124])).
% 0.20/0.67  fof(f124,plain,(
% 0.20/0.67    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.67  fof(f219,plain,(
% 0.20/0.67    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f136,f109])).
% 0.20/0.67  fof(f109,plain,(
% 0.20/0.67    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(definition_unfolding,[],[f75,f74])).
% 0.20/0.67  fof(f75,plain,(
% 0.20/0.67    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f25])).
% 0.20/0.67  fof(f25,plain,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f13])).
% 0.20/0.67  fof(f13,axiom,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.67  fof(f68,plain,(
% 0.20/0.67    v3_ordinal1(sK0)),
% 0.20/0.67    inference(cnf_transformation,[],[f47])).
% 0.20/0.67  fof(f47,plain,(
% 0.20/0.67    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 0.20/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 0.20/0.67  fof(f45,plain,(
% 0.20/0.67    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 0.20/0.67    introduced(choice_axiom,[])).
% 0.20/0.67  fof(f46,plain,(
% 0.20/0.67    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 0.20/0.67    introduced(choice_axiom,[])).
% 0.20/0.67  fof(f44,plain,(
% 0.20/0.67    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 0.20/0.67    inference(rectify,[],[f43])).
% 0.20/0.67  fof(f43,plain,(
% 0.20/0.67    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 0.20/0.67    inference(flattening,[],[f42])).
% 0.20/0.67  fof(f42,plain,(
% 0.20/0.67    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 0.20/0.67    inference(nnf_transformation,[],[f24])).
% 0.20/0.67  fof(f24,plain,(
% 0.20/0.67    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 0.20/0.67    inference(flattening,[],[f23])).
% 0.20/0.67  fof(f23,plain,(
% 0.20/0.67    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f20])).
% 0.20/0.67  fof(f20,negated_conjecture,(
% 0.20/0.67    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 0.20/0.67    inference(negated_conjecture,[],[f19])).
% 0.20/0.67  fof(f19,conjecture,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 0.20/0.67  fof(f952,plain,(
% 0.20/0.67    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f136,f610,f773,f111])).
% 0.20/0.67  fof(f111,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(definition_unfolding,[],[f77,f74])).
% 0.20/0.67  fof(f77,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f48])).
% 0.20/0.67  fof(f48,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(nnf_transformation,[],[f27])).
% 0.20/0.67  fof(f27,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f14])).
% 0.20/0.67  fof(f14,axiom,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.67  fof(f773,plain,(
% 0.20/0.67    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f606,f89])).
% 0.20/0.67  fof(f89,plain,(
% 0.20/0.67    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f35])).
% 0.20/0.67  fof(f35,plain,(
% 0.20/0.67    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.20/0.67    inference(flattening,[],[f34])).
% 0.20/0.67  fof(f34,plain,(
% 0.20/0.67    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.20/0.67    inference(ennf_transformation,[],[f11])).
% 0.20/0.67  fof(f11,axiom,(
% 0.20/0.67    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.20/0.67  fof(f606,plain,(
% 0.20/0.67    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f131,f540])).
% 0.20/0.67  fof(f540,plain,(
% 0.20/0.67    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 0.20/0.67    inference(superposition,[],[f117,f510])).
% 0.20/0.67  fof(f510,plain,(
% 0.20/0.67    sK0 = k3_tarski(sK0) | ~spl8_1),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f121,f84])).
% 0.20/0.67  fof(f84,plain,(
% 0.20/0.67    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f52])).
% 0.20/0.67  fof(f52,plain,(
% 0.20/0.67    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 0.20/0.67    inference(nnf_transformation,[],[f8])).
% 0.20/0.67  fof(f8,axiom,(
% 0.20/0.67    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 0.20/0.67  fof(f121,plain,(
% 0.20/0.67    v4_ordinal1(sK0) | ~spl8_1),
% 0.20/0.67    inference(avatar_component_clause,[],[f120])).
% 0.20/0.67  fof(f120,plain,(
% 0.20/0.67    spl8_1 <=> v4_ordinal1(sK0)),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.67  fof(f117,plain,(
% 0.20/0.67    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 0.20/0.67    inference(equality_resolution,[],[f100])).
% 0.20/0.67  fof(f100,plain,(
% 0.20/0.67    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 0.20/0.67    inference(cnf_transformation,[],[f67])).
% 0.20/0.67  fof(f67,plain,(
% 0.20/0.67    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f63,f66,f65,f64])).
% 0.20/0.67  fof(f64,plain,(
% 0.20/0.67    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.67    introduced(choice_axiom,[])).
% 0.20/0.67  fof(f65,plain,(
% 0.20/0.67    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 0.20/0.67    introduced(choice_axiom,[])).
% 0.20/0.67  fof(f66,plain,(
% 0.20/0.67    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 0.20/0.67    introduced(choice_axiom,[])).
% 0.20/0.67  fof(f63,plain,(
% 0.20/0.67    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.67    inference(rectify,[],[f62])).
% 0.20/0.67  fof(f62,plain,(
% 0.20/0.67    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.67    inference(nnf_transformation,[],[f3])).
% 0.20/0.67  fof(f3,axiom,(
% 0.20/0.67    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.67  fof(f610,plain,(
% 0.20/0.67    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f131,f541])).
% 0.20/0.67  fof(f541,plain,(
% 0.20/0.67    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 0.20/0.67    inference(superposition,[],[f118,f510])).
% 0.20/0.67  fof(f118,plain,(
% 0.20/0.67    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 0.20/0.67    inference(equality_resolution,[],[f99])).
% 0.20/0.67  fof(f99,plain,(
% 0.20/0.67    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 0.20/0.67    inference(cnf_transformation,[],[f67])).
% 0.20/0.67  fof(f1521,plain,(
% 0.20/0.67    ~r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f773,f778,f91])).
% 0.20/0.67  fof(f778,plain,(
% 0.20/0.67    ~r1_tarski(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f606,f105])).
% 0.20/0.67  fof(f509,plain,(
% 0.20/0.67    spl8_1 | ~spl8_5 | ~spl8_6),
% 0.20/0.67    inference(avatar_contradiction_clause,[],[f508])).
% 0.20/0.67  fof(f508,plain,(
% 0.20/0.67    $false | (spl8_1 | ~spl8_5 | ~spl8_6)),
% 0.20/0.67    inference(subsumption_resolution,[],[f507,f441])).
% 0.20/0.67  fof(f441,plain,(
% 0.20/0.67    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_6)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f237,f108,f207,f104])).
% 0.20/0.67  fof(f104,plain,(
% 0.20/0.67    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f67])).
% 0.20/0.67  fof(f207,plain,(
% 0.20/0.67    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_6),
% 0.20/0.67    inference(avatar_component_clause,[],[f205])).
% 0.20/0.67  fof(f205,plain,(
% 0.20/0.67    spl8_6 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.67  fof(f108,plain,(
% 0.20/0.67    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.20/0.67    inference(definition_unfolding,[],[f73,f74])).
% 0.20/0.67  fof(f73,plain,(
% 0.20/0.67    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.67    inference(cnf_transformation,[],[f10])).
% 0.20/0.67  fof(f10,axiom,(
% 0.20/0.67    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.67  fof(f237,plain,(
% 0.20/0.67    sK0 != k3_tarski(sK0) | spl8_1),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f122,f85])).
% 0.20/0.67  fof(f85,plain,(
% 0.20/0.67    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 0.20/0.67    inference(cnf_transformation,[],[f52])).
% 0.20/0.67  fof(f122,plain,(
% 0.20/0.67    ~v4_ordinal1(sK0) | spl8_1),
% 0.20/0.67    inference(avatar_component_clause,[],[f120])).
% 0.20/0.67  fof(f507,plain,(
% 0.20/0.67    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_6)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f207,f443,f140])).
% 0.20/0.67  fof(f140,plain,(
% 0.20/0.67    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 0.20/0.67    inference(avatar_component_clause,[],[f139])).
% 0.20/0.67  fof(f139,plain,(
% 0.20/0.67    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.67  fof(f443,plain,(
% 0.20/0.67    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_6),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f207,f89])).
% 0.20/0.67  fof(f435,plain,(
% 0.20/0.67    spl8_6 | ~spl8_7 | ~spl8_8),
% 0.20/0.67    inference(avatar_contradiction_clause,[],[f434])).
% 0.20/0.67  fof(f434,plain,(
% 0.20/0.67    $false | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 0.20/0.67    inference(subsumption_resolution,[],[f429,f299])).
% 0.20/0.67  fof(f299,plain,(
% 0.20/0.67    r1_tarski(sK6(sK0,sK0),sK0) | ~spl8_7),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f142,f211,f86])).
% 0.20/0.67  fof(f86,plain,(
% 0.20/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f32])).
% 0.20/0.67  fof(f32,plain,(
% 0.20/0.67    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f21])).
% 0.20/0.67  fof(f21,plain,(
% 0.20/0.67    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.20/0.67    inference(unused_predicate_definition_removal,[],[f7])).
% 0.20/0.67  fof(f7,axiom,(
% 0.20/0.67    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.20/0.67  fof(f211,plain,(
% 0.20/0.67    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_7),
% 0.20/0.67    inference(avatar_component_clause,[],[f209])).
% 0.20/0.67  fof(f209,plain,(
% 0.20/0.67    spl8_7 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.67  fof(f142,plain,(
% 0.20/0.67    v1_ordinal1(sK0)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f68,f76])).
% 0.20/0.67  fof(f76,plain,(
% 0.20/0.67    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f26])).
% 0.20/0.67  fof(f26,plain,(
% 0.20/0.67    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.20/0.67    inference(ennf_transformation,[],[f22])).
% 0.20/0.67  fof(f22,plain,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.20/0.67    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.67  fof(f4,axiom,(
% 0.20/0.67    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.67  fof(f429,plain,(
% 0.20/0.67    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_8)),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f206,f352,f96])).
% 0.20/0.67  fof(f96,plain,(
% 0.20/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f61])).
% 0.20/0.67  fof(f61,plain,(
% 0.20/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).
% 0.20/0.67  fof(f60,plain,(
% 0.20/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.67    introduced(choice_axiom,[])).
% 0.20/0.67  fof(f59,plain,(
% 0.20/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.67    inference(rectify,[],[f58])).
% 0.20/0.67  fof(f58,plain,(
% 0.20/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.67    inference(nnf_transformation,[],[f40])).
% 0.20/0.67  fof(f40,plain,(
% 0.20/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.67    inference(ennf_transformation,[],[f1])).
% 0.20/0.67  fof(f1,axiom,(
% 0.20/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.67  fof(f352,plain,(
% 0.20/0.67    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_8),
% 0.20/0.67    inference(avatar_component_clause,[],[f350])).
% 0.20/0.67  fof(f350,plain,(
% 0.20/0.67    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 0.20/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.67  fof(f206,plain,(
% 0.20/0.67    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_6),
% 0.20/0.67    inference(avatar_component_clause,[],[f205])).
% 0.20/0.67  fof(f353,plain,(
% 0.20/0.67    spl8_6 | spl8_8 | spl8_1),
% 0.20/0.67    inference(avatar_split_clause,[],[f348,f120,f350,f205])).
% 0.20/0.67  fof(f348,plain,(
% 0.20/0.67    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 0.20/0.67    inference(equality_resolution,[],[f249])).
% 0.20/0.67  fof(f249,plain,(
% 0.20/0.67    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 0.20/0.67    inference(superposition,[],[f237,f102])).
% 0.20/0.67  fof(f102,plain,(
% 0.20/0.67    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f67])).
% 0.20/0.67  fof(f212,plain,(
% 0.20/0.67    spl8_6 | spl8_7 | spl8_1),
% 0.20/0.67    inference(avatar_split_clause,[],[f203,f120,f209,f205])).
% 0.20/0.67  fof(f203,plain,(
% 0.20/0.67    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 0.20/0.67    inference(equality_resolution,[],[f157])).
% 0.20/0.67  fof(f157,plain,(
% 0.20/0.67    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 0.20/0.67    inference(superposition,[],[f152,f103])).
% 0.20/0.67  fof(f103,plain,(
% 0.20/0.67    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f67])).
% 0.20/0.67  fof(f152,plain,(
% 0.20/0.67    sK0 != k3_tarski(sK0) | spl8_1),
% 0.20/0.67    inference(unit_resulting_resolution,[],[f122,f85])).
% 0.20/0.67  fof(f141,plain,(
% 0.20/0.67    spl8_1 | spl8_5),
% 0.20/0.67    inference(avatar_split_clause,[],[f107,f139,f120])).
% 0.20/0.67  fof(f107,plain,(
% 0.20/0.67    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 0.20/0.67    inference(definition_unfolding,[],[f69,f74])).
% 0.20/0.67  fof(f69,plain,(
% 0.20/0.67    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 0.20/0.67    inference(cnf_transformation,[],[f47])).
% 0.20/0.67  fof(f137,plain,(
% 0.20/0.67    ~spl8_1 | spl8_4),
% 0.20/0.67    inference(avatar_split_clause,[],[f70,f134,f120])).
% 0.20/0.67  fof(f70,plain,(
% 0.20/0.67    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.20/0.67    inference(cnf_transformation,[],[f47])).
% 0.20/0.67  fof(f132,plain,(
% 0.20/0.67    ~spl8_1 | spl8_3),
% 0.20/0.67    inference(avatar_split_clause,[],[f71,f129,f120])).
% 0.20/0.68  fof(f71,plain,(
% 0.20/0.68    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 0.20/0.68    inference(cnf_transformation,[],[f47])).
% 0.20/0.68  fof(f127,plain,(
% 0.20/0.68    ~spl8_1 | ~spl8_2),
% 0.20/0.68    inference(avatar_split_clause,[],[f106,f124,f120])).
% 0.20/0.68  fof(f106,plain,(
% 0.20/0.68    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 0.20/0.68    inference(definition_unfolding,[],[f72,f74])).
% 0.20/0.68  fof(f72,plain,(
% 0.20/0.68    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 0.20/0.68    inference(cnf_transformation,[],[f47])).
% 0.20/0.68  % SZS output end Proof for theBenchmark
% 0.20/0.68  % (22698)------------------------------
% 0.20/0.68  % (22698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.68  % (22698)Termination reason: Refutation
% 0.20/0.68  
% 0.20/0.68  % (22698)Memory used [KB]: 11897
% 0.20/0.68  % (22698)Time elapsed: 0.274 s
% 0.20/0.68  % (22698)------------------------------
% 0.20/0.68  % (22698)------------------------------
% 0.20/0.68  % (22703)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 0.20/0.68  % (22671)Success in time 0.322 s
%------------------------------------------------------------------------------
