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
% DateTime   : Thu Dec  3 12:55:41 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 449 expanded)
%              Number of leaves         :   27 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  515 (2274 expanded)
%              Number of equality atoms :   32 ( 126 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f136,f141,f145,f222,f388,f880,f936,f2236])).

fof(f2236,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f2235])).

fof(f2235,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f2234,f1679])).

fof(f1679,plain,
    ( r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f1672,f1138])).

fof(f1138,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f130,f981,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f102,f72])).

fof(f72,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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

fof(f981,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f66,f228,f945,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f77,f72])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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

fof(f945,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f140,f66,f135,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f74,f72])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f135,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f140,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f228,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f140,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f73,f72])).

fof(f73,plain,(
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

fof(f66,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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

fof(f130,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1672,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f140,f1050,f1519,f111])).

fof(f1519,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f66,f1047,f86])).

fof(f86,plain,(
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

fof(f1047,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f135,f966])).

fof(f966,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f120,f937])).

fof(f937,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f125,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f125,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f120,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f59,f62,f61,f60])).

fof(f60,plain,(
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

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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

fof(f1050,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f135,f967])).

fof(f967,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f121,f937])).

fof(f121,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2234,plain,
    ( ~ r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f66,f1519,f1523,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f1523,plain,
    ( ~ r1_tarski(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f1047,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f936,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f935])).

fof(f935,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f934,f885])).

fof(f885,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f249,f108,f217,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f217,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f71,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f249,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f126,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f126,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f934,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f217,f888,f144])).

fof(f144,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f888,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f66,f217,f86])).

fof(f880,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f879])).

fof(f879,plain,
    ( $false
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f868,f701])).

fof(f701,plain,
    ( ~ r1_ordinal1(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f66,f394,f481,f88])).

fof(f481,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f216,f387,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f387,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f216,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f215])).

fof(f394,plain,
    ( v3_ordinal1(sK6(sK0,sK0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f66,f221,f86])).

fof(f221,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f868,plain,
    ( r1_ordinal1(sK6(sK0,sK0),sK0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f66,f394,f399,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f76,f72])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f399,plain,
    ( r2_hidden(sK6(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f221,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f103,f72])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f388,plain,
    ( spl8_6
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f383,f124,f385,f215])).

fof(f383,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f264])).

fof(f264,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f249,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f222,plain,
    ( spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f213,f124,f219,f215])).

fof(f213,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK6(sK0,X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f157,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f157,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f126,f82])).

fof(f145,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f107,f143,f124])).

fof(f107,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f67,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f141,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f68,f138,f124])).

fof(f68,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f136,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f69,f133,f124])).

fof(f69,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f131,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f106,f128,f124])).

fof(f106,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f70,f72])).

fof(f70,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (12221)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (12215)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (12237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (12223)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (12236)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (12229)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (12236)Refutation not found, incomplete strategy% (12236)------------------------------
% 0.21/0.56  % (12236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12225)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (12224)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.58  % (12216)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.58  % (12236)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (12236)Memory used [KB]: 1663
% 1.46/0.58  % (12236)Time elapsed: 0.142 s
% 1.46/0.58  % (12236)------------------------------
% 1.46/0.58  % (12236)------------------------------
% 1.46/0.58  % (12239)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.58  % (12237)Refutation not found, incomplete strategy% (12237)------------------------------
% 1.46/0.58  % (12237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (12237)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (12237)Memory used [KB]: 10746
% 1.46/0.58  % (12237)Time elapsed: 0.163 s
% 1.46/0.58  % (12237)------------------------------
% 1.46/0.58  % (12237)------------------------------
% 1.46/0.58  % (12243)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.59  % (12219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.59  % (12220)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.46/0.59  % (12218)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.59  % (12244)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.60  % (12238)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.60  % (12228)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.84/0.60  % (12234)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.84/0.60  % (12227)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.84/0.60  % (12231)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.84/0.60  % (12235)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.84/0.60  % (12242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.84/0.60  % (12235)Refutation not found, incomplete strategy% (12235)------------------------------
% 1.84/0.60  % (12235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (12235)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (12235)Memory used [KB]: 10746
% 1.84/0.60  % (12235)Time elapsed: 0.135 s
% 1.84/0.60  % (12235)------------------------------
% 1.84/0.60  % (12235)------------------------------
% 1.84/0.60  % (12230)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.84/0.61  % (12217)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.84/0.61  % (12217)Refutation not found, incomplete strategy% (12217)------------------------------
% 1.84/0.61  % (12217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (12217)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (12217)Memory used [KB]: 10746
% 1.84/0.61  % (12217)Time elapsed: 0.187 s
% 1.84/0.61  % (12217)------------------------------
% 1.84/0.61  % (12217)------------------------------
% 1.84/0.61  % (12222)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.84/0.61  % (12226)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.84/0.61  % (12241)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.84/0.62  % (12233)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.84/0.62  % (12232)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.65  % (12240)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.32/0.73  % (12282)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.32/0.73  % (12281)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.98/0.78  % (12284)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.98/0.78  % (12283)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.34/0.83  % (12241)Refutation found. Thanks to Tanya!
% 3.34/0.83  % SZS status Theorem for theBenchmark
% 3.34/0.83  % SZS output start Proof for theBenchmark
% 3.34/0.83  fof(f2237,plain,(
% 3.34/0.83    $false),
% 3.34/0.83    inference(avatar_sat_refutation,[],[f131,f136,f141,f145,f222,f388,f880,f936,f2236])).
% 3.34/0.83  fof(f2236,plain,(
% 3.34/0.83    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 3.34/0.83    inference(avatar_contradiction_clause,[],[f2235])).
% 3.34/0.83  fof(f2235,plain,(
% 3.34/0.83    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.34/0.83    inference(subsumption_resolution,[],[f2234,f1679])).
% 3.34/0.83  fof(f1679,plain,(
% 3.34/0.83    r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.34/0.83    inference(forward_demodulation,[],[f1672,f1138])).
% 3.34/0.83  fof(f1138,plain,(
% 3.34/0.83    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f130,f981,f116])).
% 3.34/0.83  fof(f116,plain,(
% 3.34/0.83    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 3.34/0.83    inference(definition_unfolding,[],[f102,f72])).
% 3.34/0.83  fof(f72,plain,(
% 3.34/0.83    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.34/0.83    inference(cnf_transformation,[],[f5])).
% 3.34/0.83  fof(f5,axiom,(
% 3.34/0.83    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 3.34/0.83  fof(f102,plain,(
% 3.34/0.83    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 3.34/0.83    inference(cnf_transformation,[],[f65])).
% 3.34/0.83  fof(f65,plain,(
% 3.34/0.83    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.34/0.83    inference(flattening,[],[f64])).
% 3.34/0.83  fof(f64,plain,(
% 3.34/0.83    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.34/0.83    inference(nnf_transformation,[],[f9])).
% 3.34/0.83  fof(f9,axiom,(
% 3.34/0.83    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 3.34/0.83  fof(f981,plain,(
% 3.34/0.83    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),k2_xboole_0(sK0,k1_tarski(sK0))) | (~spl8_3 | ~spl8_4)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f228,f945,f112])).
% 3.34/0.83  fof(f112,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(definition_unfolding,[],[f77,f72])).
% 3.34/0.83  fof(f77,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f45])).
% 3.34/0.83  fof(f45,plain,(
% 3.34/0.83    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(nnf_transformation,[],[f24])).
% 3.34/0.83  fof(f24,plain,(
% 3.34/0.83    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(ennf_transformation,[],[f14])).
% 3.34/0.83  fof(f14,axiom,(
% 3.34/0.83    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 3.34/0.83  fof(f945,plain,(
% 3.34/0.83    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | (~spl8_3 | ~spl8_4)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f140,f66,f135,f111])).
% 3.34/0.83  fof(f111,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(definition_unfolding,[],[f74,f72])).
% 3.34/0.83  fof(f74,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f44])).
% 3.34/0.83  fof(f44,plain,(
% 3.34/0.83    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(nnf_transformation,[],[f23])).
% 3.34/0.83  fof(f23,plain,(
% 3.34/0.83    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(ennf_transformation,[],[f13])).
% 3.34/0.83  fof(f13,axiom,(
% 3.34/0.83    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 3.34/0.83  fof(f135,plain,(
% 3.34/0.83    r2_hidden(sK1,sK0) | ~spl8_3),
% 3.34/0.83    inference(avatar_component_clause,[],[f133])).
% 3.34/0.83  fof(f133,plain,(
% 3.34/0.83    spl8_3 <=> r2_hidden(sK1,sK0)),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.34/0.83  fof(f140,plain,(
% 3.34/0.83    v3_ordinal1(sK1) | ~spl8_4),
% 3.34/0.83    inference(avatar_component_clause,[],[f138])).
% 3.34/0.83  fof(f138,plain,(
% 3.34/0.83    spl8_4 <=> v3_ordinal1(sK1)),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.34/0.83  fof(f228,plain,(
% 3.34/0.83    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f140,f109])).
% 3.34/0.83  fof(f109,plain,(
% 3.34/0.83    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(definition_unfolding,[],[f73,f72])).
% 3.34/0.83  fof(f73,plain,(
% 3.34/0.83    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f22])).
% 3.34/0.83  fof(f22,plain,(
% 3.34/0.83    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(ennf_transformation,[],[f12])).
% 3.34/0.83  fof(f12,axiom,(
% 3.34/0.83    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 3.34/0.83  fof(f66,plain,(
% 3.34/0.83    v3_ordinal1(sK0)),
% 3.34/0.83    inference(cnf_transformation,[],[f43])).
% 3.34/0.83  fof(f43,plain,(
% 3.34/0.83    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 3.34/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 3.34/0.83  fof(f41,plain,(
% 3.34/0.83    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 3.34/0.83    introduced(choice_axiom,[])).
% 3.34/0.83  fof(f42,plain,(
% 3.34/0.83    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 3.34/0.83    introduced(choice_axiom,[])).
% 3.34/0.83  fof(f40,plain,(
% 3.34/0.83    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.34/0.83    inference(rectify,[],[f39])).
% 3.34/0.83  fof(f39,plain,(
% 3.34/0.83    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.34/0.83    inference(flattening,[],[f38])).
% 3.34/0.83  fof(f38,plain,(
% 3.34/0.83    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.34/0.83    inference(nnf_transformation,[],[f21])).
% 3.34/0.83  fof(f21,plain,(
% 3.34/0.83    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.34/0.83    inference(flattening,[],[f20])).
% 3.34/0.83  fof(f20,plain,(
% 3.34/0.83    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.34/0.83    inference(ennf_transformation,[],[f19])).
% 3.34/0.83  fof(f19,negated_conjecture,(
% 3.34/0.83    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.34/0.83    inference(negated_conjecture,[],[f18])).
% 3.34/0.83  fof(f18,conjecture,(
% 3.34/0.83    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 3.34/0.83  fof(f130,plain,(
% 3.34/0.83    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 3.34/0.83    inference(avatar_component_clause,[],[f128])).
% 3.34/0.83  fof(f128,plain,(
% 3.34/0.83    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.34/0.83  fof(f1672,plain,(
% 3.34/0.83    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f140,f1050,f1519,f111])).
% 3.34/0.83  fof(f1519,plain,(
% 3.34/0.83    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f1047,f86])).
% 3.34/0.83  fof(f86,plain,(
% 3.34/0.83    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f31])).
% 3.34/0.83  fof(f31,plain,(
% 3.34/0.83    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.34/0.83    inference(flattening,[],[f30])).
% 3.34/0.83  fof(f30,plain,(
% 3.34/0.83    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.34/0.83    inference(ennf_transformation,[],[f10])).
% 3.34/0.83  fof(f10,axiom,(
% 3.34/0.83    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 3.34/0.83  fof(f1047,plain,(
% 3.34/0.83    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f135,f966])).
% 3.34/0.83  fof(f966,plain,(
% 3.34/0.83    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 3.34/0.83    inference(superposition,[],[f120,f937])).
% 3.34/0.83  fof(f937,plain,(
% 3.34/0.83    sK0 = k3_tarski(sK0) | ~spl8_1),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f125,f81])).
% 3.34/0.83  fof(f81,plain,(
% 3.34/0.83    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f48])).
% 3.34/0.83  fof(f48,plain,(
% 3.34/0.83    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 3.34/0.83    inference(nnf_transformation,[],[f6])).
% 3.34/0.83  fof(f6,axiom,(
% 3.34/0.83    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 3.34/0.83  fof(f125,plain,(
% 3.34/0.83    v4_ordinal1(sK0) | ~spl8_1),
% 3.34/0.83    inference(avatar_component_clause,[],[f124])).
% 3.34/0.83  fof(f124,plain,(
% 3.34/0.83    spl8_1 <=> v4_ordinal1(sK0)),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.34/0.83  fof(f120,plain,(
% 3.34/0.83    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.34/0.83    inference(equality_resolution,[],[f97])).
% 3.34/0.83  fof(f97,plain,(
% 3.34/0.83    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.34/0.83    inference(cnf_transformation,[],[f63])).
% 3.34/0.83  fof(f63,plain,(
% 3.34/0.83    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.34/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f59,f62,f61,f60])).
% 3.34/0.83  fof(f60,plain,(
% 3.34/0.83    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 3.34/0.83    introduced(choice_axiom,[])).
% 3.34/0.83  fof(f61,plain,(
% 3.34/0.83    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 3.34/0.83    introduced(choice_axiom,[])).
% 3.34/0.83  fof(f62,plain,(
% 3.34/0.83    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 3.34/0.83    introduced(choice_axiom,[])).
% 3.34/0.83  fof(f59,plain,(
% 3.34/0.83    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.34/0.83    inference(rectify,[],[f58])).
% 3.34/0.83  fof(f58,plain,(
% 3.34/0.83    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.34/0.83    inference(nnf_transformation,[],[f3])).
% 3.34/0.83  fof(f3,axiom,(
% 3.34/0.83    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 3.34/0.83  fof(f1050,plain,(
% 3.34/0.83    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f135,f967])).
% 3.34/0.83  fof(f967,plain,(
% 3.34/0.83    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 3.34/0.83    inference(superposition,[],[f121,f937])).
% 3.34/0.83  fof(f121,plain,(
% 3.34/0.83    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.34/0.83    inference(equality_resolution,[],[f96])).
% 3.34/0.83  fof(f96,plain,(
% 3.34/0.83    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.34/0.83    inference(cnf_transformation,[],[f63])).
% 3.34/0.83  fof(f2234,plain,(
% 3.34/0.83    ~r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f1519,f1523,f88])).
% 3.34/0.83  fof(f88,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f51])).
% 3.34/0.83  fof(f51,plain,(
% 3.34/0.83    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(nnf_transformation,[],[f35])).
% 3.34/0.83  fof(f35,plain,(
% 3.34/0.83    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.34/0.83    inference(flattening,[],[f34])).
% 3.34/0.83  fof(f34,plain,(
% 3.34/0.83    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.34/0.83    inference(ennf_transformation,[],[f7])).
% 3.34/0.83  fof(f7,axiom,(
% 3.34/0.83    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 3.34/0.83  fof(f1523,plain,(
% 3.34/0.83    ~r1_tarski(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f1047,f105])).
% 3.34/0.83  fof(f105,plain,(
% 3.34/0.83    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f37])).
% 3.34/0.83  fof(f37,plain,(
% 3.34/0.83    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.34/0.83    inference(ennf_transformation,[],[f17])).
% 3.34/0.83  fof(f17,axiom,(
% 3.34/0.83    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.34/0.83  fof(f936,plain,(
% 3.34/0.83    spl8_1 | ~spl8_5 | ~spl8_6),
% 3.34/0.83    inference(avatar_contradiction_clause,[],[f935])).
% 3.34/0.83  fof(f935,plain,(
% 3.34/0.83    $false | (spl8_1 | ~spl8_5 | ~spl8_6)),
% 3.34/0.83    inference(subsumption_resolution,[],[f934,f885])).
% 3.34/0.83  fof(f885,plain,(
% 3.34/0.83    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_6)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f249,f108,f217,f101])).
% 3.34/0.83  fof(f101,plain,(
% 3.34/0.83    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f63])).
% 3.34/0.83  fof(f217,plain,(
% 3.34/0.83    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_6),
% 3.34/0.83    inference(avatar_component_clause,[],[f215])).
% 3.34/0.83  fof(f215,plain,(
% 3.34/0.83    spl8_6 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.34/0.83  fof(f108,plain,(
% 3.34/0.83    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 3.34/0.83    inference(definition_unfolding,[],[f71,f72])).
% 3.34/0.83  fof(f71,plain,(
% 3.34/0.83    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.34/0.83    inference(cnf_transformation,[],[f8])).
% 3.34/0.83  fof(f8,axiom,(
% 3.34/0.83    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 3.34/0.83  fof(f249,plain,(
% 3.34/0.83    sK0 != k3_tarski(sK0) | spl8_1),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f126,f82])).
% 3.34/0.83  fof(f82,plain,(
% 3.34/0.83    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 3.34/0.83    inference(cnf_transformation,[],[f48])).
% 3.34/0.83  fof(f126,plain,(
% 3.34/0.83    ~v4_ordinal1(sK0) | spl8_1),
% 3.34/0.83    inference(avatar_component_clause,[],[f124])).
% 3.34/0.83  fof(f934,plain,(
% 3.34/0.83    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_6)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f217,f888,f144])).
% 3.34/0.83  fof(f144,plain,(
% 3.34/0.83    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 3.34/0.83    inference(avatar_component_clause,[],[f143])).
% 3.34/0.83  fof(f143,plain,(
% 3.34/0.83    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.34/0.83  fof(f888,plain,(
% 3.34/0.83    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_6),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f217,f86])).
% 3.34/0.83  fof(f880,plain,(
% 3.34/0.83    spl8_6 | ~spl8_7 | ~spl8_8),
% 3.34/0.83    inference(avatar_contradiction_clause,[],[f879])).
% 3.34/0.83  fof(f879,plain,(
% 3.34/0.83    $false | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 3.34/0.83    inference(subsumption_resolution,[],[f868,f701])).
% 3.34/0.83  fof(f701,plain,(
% 3.34/0.83    ~r1_ordinal1(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f394,f481,f88])).
% 3.34/0.83  fof(f481,plain,(
% 3.34/0.83    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_6 | ~spl8_8)),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f216,f387,f93])).
% 3.34/0.83  fof(f93,plain,(
% 3.34/0.83    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f57])).
% 3.34/0.83  fof(f57,plain,(
% 3.34/0.83    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 3.34/0.83  fof(f56,plain,(
% 3.34/0.83    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.34/0.83    introduced(choice_axiom,[])).
% 3.34/0.83  fof(f55,plain,(
% 3.34/0.83    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/0.83    inference(rectify,[],[f54])).
% 3.34/0.83  fof(f54,plain,(
% 3.34/0.83    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/0.83    inference(nnf_transformation,[],[f36])).
% 3.34/0.83  fof(f36,plain,(
% 3.34/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.34/0.83    inference(ennf_transformation,[],[f1])).
% 3.34/0.83  fof(f1,axiom,(
% 3.34/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.34/0.83  fof(f387,plain,(
% 3.34/0.83    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_8),
% 3.34/0.83    inference(avatar_component_clause,[],[f385])).
% 3.34/0.83  fof(f385,plain,(
% 3.34/0.83    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.34/0.83  fof(f216,plain,(
% 3.34/0.83    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_6),
% 3.34/0.83    inference(avatar_component_clause,[],[f215])).
% 3.34/0.83  fof(f394,plain,(
% 3.34/0.83    v3_ordinal1(sK6(sK0,sK0)) | ~spl8_7),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f221,f86])).
% 3.34/0.83  fof(f221,plain,(
% 3.34/0.83    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_7),
% 3.34/0.83    inference(avatar_component_clause,[],[f219])).
% 3.34/0.83  fof(f219,plain,(
% 3.34/0.83    spl8_7 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 3.34/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.34/0.83  fof(f868,plain,(
% 3.34/0.83    r1_ordinal1(sK6(sK0,sK0),sK0) | ~spl8_7),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f66,f394,f399,f113])).
% 3.34/0.83  fof(f113,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(definition_unfolding,[],[f76,f72])).
% 3.34/0.83  fof(f76,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f45])).
% 3.34/0.83  fof(f399,plain,(
% 3.34/0.83    r2_hidden(sK6(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl8_7),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f221,f115])).
% 3.34/0.83  fof(f115,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 3.34/0.83    inference(definition_unfolding,[],[f103,f72])).
% 3.34/0.83  fof(f103,plain,(
% 3.34/0.83    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f65])).
% 3.34/0.83  fof(f388,plain,(
% 3.34/0.83    spl8_6 | spl8_8 | spl8_1),
% 3.34/0.83    inference(avatar_split_clause,[],[f383,f124,f385,f215])).
% 3.34/0.83  fof(f383,plain,(
% 3.34/0.83    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 3.34/0.83    inference(equality_resolution,[],[f264])).
% 3.34/0.83  fof(f264,plain,(
% 3.34/0.83    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 3.34/0.83    inference(superposition,[],[f249,f99])).
% 3.34/0.83  fof(f99,plain,(
% 3.34/0.83    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f63])).
% 3.34/0.83  fof(f222,plain,(
% 3.34/0.83    spl8_6 | spl8_7 | spl8_1),
% 3.34/0.83    inference(avatar_split_clause,[],[f213,f124,f219,f215])).
% 3.34/0.83  fof(f213,plain,(
% 3.34/0.83    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 3.34/0.83    inference(equality_resolution,[],[f162])).
% 3.34/0.83  fof(f162,plain,(
% 3.34/0.83    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 3.34/0.83    inference(superposition,[],[f157,f100])).
% 3.34/0.83  fof(f100,plain,(
% 3.34/0.83    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f63])).
% 3.34/0.83  fof(f157,plain,(
% 3.34/0.83    sK0 != k3_tarski(sK0) | spl8_1),
% 3.34/0.83    inference(unit_resulting_resolution,[],[f126,f82])).
% 3.34/0.83  fof(f145,plain,(
% 3.34/0.83    spl8_1 | spl8_5),
% 3.34/0.83    inference(avatar_split_clause,[],[f107,f143,f124])).
% 3.34/0.83  fof(f107,plain,(
% 3.34/0.83    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.34/0.83    inference(definition_unfolding,[],[f67,f72])).
% 3.34/0.83  fof(f67,plain,(
% 3.34/0.83    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.34/0.83    inference(cnf_transformation,[],[f43])).
% 3.34/0.83  fof(f141,plain,(
% 3.34/0.83    ~spl8_1 | spl8_4),
% 3.34/0.83    inference(avatar_split_clause,[],[f68,f138,f124])).
% 3.34/0.83  fof(f68,plain,(
% 3.34/0.83    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 3.34/0.83    inference(cnf_transformation,[],[f43])).
% 3.34/0.83  fof(f136,plain,(
% 3.34/0.83    ~spl8_1 | spl8_3),
% 3.34/0.83    inference(avatar_split_clause,[],[f69,f133,f124])).
% 3.34/0.83  fof(f69,plain,(
% 3.34/0.83    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 3.34/0.83    inference(cnf_transformation,[],[f43])).
% 3.34/0.83  fof(f131,plain,(
% 3.34/0.83    ~spl8_1 | ~spl8_2),
% 3.34/0.83    inference(avatar_split_clause,[],[f106,f128,f124])).
% 3.34/0.83  fof(f106,plain,(
% 3.34/0.83    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 3.34/0.83    inference(definition_unfolding,[],[f70,f72])).
% 3.34/0.83  fof(f70,plain,(
% 3.34/0.83    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 3.34/0.83    inference(cnf_transformation,[],[f43])).
% 3.34/0.83  % SZS output end Proof for theBenchmark
% 3.34/0.83  % (12241)------------------------------
% 3.34/0.83  % (12241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.83  % (12241)Termination reason: Refutation
% 3.34/0.83  
% 3.34/0.83  % (12241)Memory used [KB]: 12153
% 3.34/0.83  % (12241)Time elapsed: 0.407 s
% 3.34/0.83  % (12241)------------------------------
% 3.34/0.83  % (12241)------------------------------
% 3.34/0.84  % (12220)Time limit reached!
% 3.34/0.84  % (12220)------------------------------
% 3.34/0.84  % (12220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.84  % (12220)Termination reason: Time limit
% 3.34/0.84  % (12220)Termination phase: Saturation
% 3.34/0.84  
% 3.34/0.84  % (12220)Memory used [KB]: 8187
% 3.34/0.84  % (12220)Time elapsed: 0.400 s
% 3.34/0.84  % (12220)------------------------------
% 3.34/0.84  % (12220)------------------------------
% 3.34/0.85  % (12214)Success in time 0.483 s
%------------------------------------------------------------------------------
