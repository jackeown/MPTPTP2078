%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:40 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 489 expanded)
%              Number of leaves         :   28 ( 154 expanded)
%              Depth                    :   15
%              Number of atoms          :  520 (2543 expanded)
%              Number of equality atoms :   28 ( 110 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f128,f133,f137,f241,f398,f407,f1906,f2465])).

fof(f2465,plain,
    ( spl8_8
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f2464])).

fof(f2464,plain,
    ( $false
    | spl8_8
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f2459,f2262])).

fof(f2262,plain,
    ( ~ r1_ordinal1(sK6(sK0,sK0),sK0)
    | spl8_8
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f64,f2023,f2049,f87])).

fof(f87,plain,(
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

fof(f2049,plain,
    ( ~ r1_tarski(sK6(sK0,sK0),sK0)
    | spl8_8
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f235,f406,f92])).

fof(f92,plain,(
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

fof(f406,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl8_15
  <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f235,plain,
    ( ~ r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl8_8
  <=> r2_hidden(sK5(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f2023,plain,
    ( v3_ordinal1(sK6(sK0,sK0))
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f64,f240,f85])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f240,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl8_9
  <=> r2_hidden(sK6(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f2459,plain,
    ( r1_ordinal1(sK6(sK0,sK0),sK0)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f64,f2023,f2184,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f2184,plain,
    ( ~ r1_ordinal1(sK0,sK6(sK0,sK0))
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f64,f2023,f2027,f87])).

fof(f2027,plain,
    ( ~ r1_tarski(sK0,sK6(sK0,sK0))
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f240,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1906,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f1905])).

fof(f1905,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1904,f1287])).

fof(f1287,plain,
    ( r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f1282,f1021])).

fof(f1021,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f414,f122,f468,f76])).

fof(f76,plain,(
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

fof(f468,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f132,f444,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f74,f70])).

fof(f70,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f444,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f132,f425,f87])).

fof(f425,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f127,f101])).

fof(f127,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f132,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f122,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f414,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f71,f70])).

fof(f71,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f1282,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f650,f977,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f977,plain,
    ( v3_ordinal1(sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f64,f648,f85])).

fof(f648,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f127,f454])).

fof(f454,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK7(sK0,X6),sK0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f113,f408])).

fof(f408,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f117,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f117,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f113,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
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

fof(f650,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f127,f455])).

fof(f455,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK7(sK0,X7)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f114,f408])).

fof(f114,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1904,plain,
    ( ~ r1_ordinal1(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f64,f977,f981,f87])).

fof(f981,plain,
    ( ~ r1_tarski(sK0,sK7(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f648,f101])).

fof(f407,plain,
    ( spl8_8
    | spl8_15
    | spl8_1 ),
    inference(avatar_split_clause,[],[f242,f116,f404,f234])).

fof(f242,plain,
    ( r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(sK0,X0),sK6(sK0,X0))
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f148,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f148,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f118,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f118,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f398,plain,
    ( spl8_1
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f396,f267])).

fof(f267,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f148,f104,f236,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f236,plain,
    ( r2_hidden(sK5(sK0,sK0),sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f234])).

fof(f104,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f69,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f396,plain,
    ( r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0)
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f236,f268,f136])).

fof(f136,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f268,plain,
    ( v3_ordinal1(sK5(sK0,sK0))
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f64,f236,f85])).

fof(f241,plain,
    ( spl8_8
    | spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f232,f116,f238,f234])).

fof(f232,plain,
    ( r2_hidden(sK6(sK0,sK0),sK0)
    | r2_hidden(sK5(sK0,sK0),sK0)
    | spl8_1 ),
    inference(equality_resolution,[],[f153])).

fof(f153,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK6(sK0,X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f148,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f137,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f103,f135,f116])).

fof(f103,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f65,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f66,f130,f116])).

fof(f66,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f128,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f67,f125,f116])).

fof(f67,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f123,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f102,f120,f116])).

fof(f102,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f68,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (13435)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (13451)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (13443)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (13443)Refutation not found, incomplete strategy% (13443)------------------------------
% 0.21/0.52  % (13443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13443)Memory used [KB]: 1663
% 0.21/0.52  % (13443)Time elapsed: 0.112 s
% 0.21/0.52  % (13443)------------------------------
% 0.21/0.52  % (13443)------------------------------
% 1.29/0.52  % (13444)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.52  % (13444)Refutation not found, incomplete strategy% (13444)------------------------------
% 1.29/0.52  % (13444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (13444)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.52  
% 1.29/0.52  % (13444)Memory used [KB]: 10746
% 1.29/0.52  % (13444)Time elapsed: 0.092 s
% 1.29/0.52  % (13444)------------------------------
% 1.29/0.52  % (13444)------------------------------
% 1.29/0.53  % (13426)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (13436)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (13425)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (13434)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (13448)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.53  % (13424)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (13423)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (13428)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (13424)Refutation not found, incomplete strategy% (13424)------------------------------
% 1.29/0.53  % (13424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (13424)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (13424)Memory used [KB]: 10746
% 1.29/0.53  % (13424)Time elapsed: 0.135 s
% 1.29/0.53  % (13424)------------------------------
% 1.29/0.53  % (13424)------------------------------
% 1.29/0.54  % (13447)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (13445)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.54  % (13449)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (13446)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.54  % (13422)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.54  % (13429)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.54  % (13440)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.54  % (13427)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.54  % (13442)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (13442)Refutation not found, incomplete strategy% (13442)------------------------------
% 1.40/0.54  % (13442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (13442)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (13442)Memory used [KB]: 10746
% 1.40/0.54  % (13442)Time elapsed: 0.141 s
% 1.40/0.54  % (13442)------------------------------
% 1.40/0.54  % (13442)------------------------------
% 1.40/0.54  % (13439)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.54  % (13441)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.54  % (13450)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (13432)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.54  % (13438)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (13431)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.55  % (13437)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (13433)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (13430)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.01/0.63  % (13452)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.01/0.67  % (13453)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.01/0.67  % (13455)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.01/0.68  % (13454)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.42/0.76  % (13448)Refutation found. Thanks to Tanya!
% 2.42/0.76  % SZS status Theorem for theBenchmark
% 2.42/0.76  % SZS output start Proof for theBenchmark
% 2.42/0.76  fof(f2466,plain,(
% 2.42/0.76    $false),
% 2.42/0.76    inference(avatar_sat_refutation,[],[f123,f128,f133,f137,f241,f398,f407,f1906,f2465])).
% 2.42/0.76  fof(f2465,plain,(
% 2.42/0.76    spl8_8 | ~spl8_9 | ~spl8_15),
% 2.42/0.76    inference(avatar_contradiction_clause,[],[f2464])).
% 2.42/0.76  fof(f2464,plain,(
% 2.42/0.76    $false | (spl8_8 | ~spl8_9 | ~spl8_15)),
% 2.42/0.76    inference(subsumption_resolution,[],[f2459,f2262])).
% 2.42/0.76  fof(f2262,plain,(
% 2.42/0.76    ~r1_ordinal1(sK6(sK0,sK0),sK0) | (spl8_8 | ~spl8_9 | ~spl8_15)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f2023,f2049,f87])).
% 2.42/0.76  fof(f87,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f51])).
% 2.42/0.76  fof(f51,plain,(
% 2.42/0.76    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(nnf_transformation,[],[f33])).
% 2.42/0.76  fof(f33,plain,(
% 2.42/0.76    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(flattening,[],[f32])).
% 2.42/0.76  fof(f32,plain,(
% 2.42/0.76    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.42/0.76    inference(ennf_transformation,[],[f7])).
% 2.42/0.76  fof(f7,axiom,(
% 2.42/0.76    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 2.42/0.76  fof(f2049,plain,(
% 2.42/0.76    ~r1_tarski(sK6(sK0,sK0),sK0) | (spl8_8 | ~spl8_15)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f235,f406,f92])).
% 2.42/0.76  fof(f92,plain,(
% 2.42/0.76    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f57])).
% 2.42/0.76  fof(f57,plain,(
% 2.42/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.42/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 2.42/0.76  fof(f56,plain,(
% 2.42/0.76    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.42/0.76    introduced(choice_axiom,[])).
% 2.42/0.76  fof(f55,plain,(
% 2.42/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.42/0.76    inference(rectify,[],[f54])).
% 2.42/0.76  fof(f54,plain,(
% 2.42/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.42/0.76    inference(nnf_transformation,[],[f34])).
% 2.42/0.76  fof(f34,plain,(
% 2.42/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.42/0.76    inference(ennf_transformation,[],[f1])).
% 2.42/0.76  fof(f1,axiom,(
% 2.42/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.42/0.76  fof(f406,plain,(
% 2.42/0.76    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | ~spl8_15),
% 2.42/0.76    inference(avatar_component_clause,[],[f404])).
% 2.42/0.76  fof(f404,plain,(
% 2.42/0.76    spl8_15 <=> r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0))),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 2.42/0.76  fof(f235,plain,(
% 2.42/0.76    ~r2_hidden(sK5(sK0,sK0),sK0) | spl8_8),
% 2.42/0.76    inference(avatar_component_clause,[],[f234])).
% 2.42/0.76  fof(f234,plain,(
% 2.42/0.76    spl8_8 <=> r2_hidden(sK5(sK0,sK0),sK0)),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.42/0.76  fof(f2023,plain,(
% 2.42/0.76    v3_ordinal1(sK6(sK0,sK0)) | ~spl8_9),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f240,f85])).
% 2.42/0.76  fof(f85,plain,(
% 2.42/0.76    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f29])).
% 2.42/0.76  fof(f29,plain,(
% 2.42/0.76    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.42/0.76    inference(flattening,[],[f28])).
% 2.42/0.76  fof(f28,plain,(
% 2.42/0.76    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.42/0.76    inference(ennf_transformation,[],[f10])).
% 2.42/0.76  fof(f10,axiom,(
% 2.42/0.76    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 2.42/0.76  fof(f240,plain,(
% 2.42/0.76    r2_hidden(sK6(sK0,sK0),sK0) | ~spl8_9),
% 2.42/0.76    inference(avatar_component_clause,[],[f238])).
% 2.42/0.76  fof(f238,plain,(
% 2.42/0.76    spl8_9 <=> r2_hidden(sK6(sK0,sK0),sK0)),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.42/0.76  fof(f64,plain,(
% 2.42/0.76    v3_ordinal1(sK0)),
% 2.42/0.76    inference(cnf_transformation,[],[f41])).
% 2.42/0.76  fof(f41,plain,(
% 2.42/0.76    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 2.42/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 2.42/0.76  fof(f39,plain,(
% 2.42/0.76    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 2.42/0.76    introduced(choice_axiom,[])).
% 2.42/0.76  fof(f40,plain,(
% 2.42/0.76    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 2.42/0.76    introduced(choice_axiom,[])).
% 2.42/0.76  fof(f38,plain,(
% 2.42/0.76    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.42/0.76    inference(rectify,[],[f37])).
% 2.42/0.76  fof(f37,plain,(
% 2.42/0.76    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.42/0.76    inference(flattening,[],[f36])).
% 2.42/0.76  fof(f36,plain,(
% 2.42/0.76    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.42/0.76    inference(nnf_transformation,[],[f20])).
% 2.42/0.76  fof(f20,plain,(
% 2.42/0.76    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.42/0.76    inference(flattening,[],[f19])).
% 2.42/0.76  fof(f19,plain,(
% 2.42/0.76    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.42/0.76    inference(ennf_transformation,[],[f18])).
% 2.42/0.76  fof(f18,negated_conjecture,(
% 2.42/0.76    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.42/0.76    inference(negated_conjecture,[],[f17])).
% 2.42/0.76  fof(f17,conjecture,(
% 2.42/0.76    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 2.42/0.76  fof(f2459,plain,(
% 2.42/0.76    r1_ordinal1(sK6(sK0,sK0),sK0) | ~spl8_9),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f2023,f2184,f86])).
% 2.42/0.76  fof(f86,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f31])).
% 2.42/0.76  fof(f31,plain,(
% 2.42/0.76    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(flattening,[],[f30])).
% 2.42/0.76  fof(f30,plain,(
% 2.42/0.76    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.42/0.76    inference(ennf_transformation,[],[f4])).
% 2.42/0.76  fof(f4,axiom,(
% 2.42/0.76    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 2.42/0.76  fof(f2184,plain,(
% 2.42/0.76    ~r1_ordinal1(sK0,sK6(sK0,sK0)) | ~spl8_9),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f2023,f2027,f87])).
% 2.42/0.76  fof(f2027,plain,(
% 2.42/0.76    ~r1_tarski(sK0,sK6(sK0,sK0)) | ~spl8_9),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f240,f101])).
% 2.42/0.76  fof(f101,plain,(
% 2.42/0.76    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f35])).
% 2.42/0.76  fof(f35,plain,(
% 2.42/0.76    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.42/0.76    inference(ennf_transformation,[],[f16])).
% 2.42/0.76  fof(f16,axiom,(
% 2.42/0.76    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.42/0.76  fof(f1906,plain,(
% 2.42/0.76    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4),
% 2.42/0.76    inference(avatar_contradiction_clause,[],[f1905])).
% 2.42/0.76  fof(f1905,plain,(
% 2.42/0.76    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.42/0.76    inference(subsumption_resolution,[],[f1904,f1287])).
% 2.42/0.76  fof(f1287,plain,(
% 2.42/0.76    r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.42/0.76    inference(forward_demodulation,[],[f1282,f1021])).
% 2.42/0.76  fof(f1021,plain,(
% 2.42/0.76    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f414,f122,f468,f76])).
% 2.42/0.76  fof(f76,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f25])).
% 2.42/0.76  fof(f25,plain,(
% 2.42/0.76    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(flattening,[],[f24])).
% 2.42/0.76  fof(f24,plain,(
% 2.42/0.76    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(ennf_transformation,[],[f11])).
% 2.42/0.76  fof(f11,axiom,(
% 2.42/0.76    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 2.42/0.76  fof(f468,plain,(
% 2.42/0.76    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_3 | ~spl8_4)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f132,f444,f109])).
% 2.42/0.76  fof(f109,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(definition_unfolding,[],[f74,f70])).
% 2.42/0.76  fof(f70,plain,(
% 2.42/0.76    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.42/0.76    inference(cnf_transformation,[],[f5])).
% 2.42/0.76  fof(f5,axiom,(
% 2.42/0.76    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.42/0.76  fof(f74,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f43])).
% 2.42/0.76  fof(f43,plain,(
% 2.42/0.76    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(nnf_transformation,[],[f23])).
% 2.42/0.76  fof(f23,plain,(
% 2.42/0.76    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(ennf_transformation,[],[f14])).
% 2.42/0.76  fof(f14,axiom,(
% 2.42/0.76    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 2.42/0.76  fof(f444,plain,(
% 2.42/0.76    ~r1_ordinal1(sK0,sK1) | (~spl8_3 | ~spl8_4)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f132,f425,f87])).
% 2.42/0.76  fof(f425,plain,(
% 2.42/0.76    ~r1_tarski(sK0,sK1) | ~spl8_3),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f127,f101])).
% 2.42/0.76  fof(f127,plain,(
% 2.42/0.76    r2_hidden(sK1,sK0) | ~spl8_3),
% 2.42/0.76    inference(avatar_component_clause,[],[f125])).
% 2.42/0.76  fof(f125,plain,(
% 2.42/0.76    spl8_3 <=> r2_hidden(sK1,sK0)),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.42/0.76  fof(f132,plain,(
% 2.42/0.76    v3_ordinal1(sK1) | ~spl8_4),
% 2.42/0.76    inference(avatar_component_clause,[],[f130])).
% 2.42/0.76  fof(f130,plain,(
% 2.42/0.76    spl8_4 <=> v3_ordinal1(sK1)),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.42/0.76  fof(f122,plain,(
% 2.42/0.76    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_2),
% 2.42/0.76    inference(avatar_component_clause,[],[f120])).
% 2.42/0.76  fof(f120,plain,(
% 2.42/0.76    spl8_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.42/0.76  fof(f414,plain,(
% 2.42/0.76    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_4),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f132,f105])).
% 2.42/0.76  fof(f105,plain,(
% 2.42/0.76    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(definition_unfolding,[],[f71,f70])).
% 2.42/0.76  fof(f71,plain,(
% 2.42/0.76    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f21])).
% 2.42/0.76  fof(f21,plain,(
% 2.42/0.76    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(ennf_transformation,[],[f12])).
% 2.42/0.76  fof(f12,axiom,(
% 2.42/0.76    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 2.42/0.76  fof(f1282,plain,(
% 2.42/0.76    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_4)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f132,f650,f977,f107])).
% 2.42/0.76  fof(f107,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(definition_unfolding,[],[f72,f70])).
% 2.42/0.76  fof(f72,plain,(
% 2.42/0.76    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f42])).
% 2.42/0.76  fof(f42,plain,(
% 2.42/0.76    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(nnf_transformation,[],[f22])).
% 2.42/0.76  fof(f22,plain,(
% 2.42/0.76    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.42/0.76    inference(ennf_transformation,[],[f13])).
% 2.42/0.76  fof(f13,axiom,(
% 2.42/0.76    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 2.42/0.76  fof(f977,plain,(
% 2.42/0.76    v3_ordinal1(sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f648,f85])).
% 2.42/0.76  fof(f648,plain,(
% 2.42/0.76    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_1 | ~spl8_3)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f127,f454])).
% 2.42/0.76  fof(f454,plain,(
% 2.42/0.76    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK7(sK0,X6),sK0)) ) | ~spl8_1),
% 2.42/0.76    inference(superposition,[],[f113,f408])).
% 2.42/0.76  fof(f408,plain,(
% 2.42/0.76    sK0 = k3_tarski(sK0) | ~spl8_1),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f117,f77])).
% 2.42/0.76  fof(f77,plain,(
% 2.42/0.76    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f44])).
% 2.42/0.76  fof(f44,plain,(
% 2.42/0.76    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 2.42/0.76    inference(nnf_transformation,[],[f6])).
% 2.42/0.76  fof(f6,axiom,(
% 2.42/0.76    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 2.42/0.76  fof(f117,plain,(
% 2.42/0.76    v4_ordinal1(sK0) | ~spl8_1),
% 2.42/0.76    inference(avatar_component_clause,[],[f116])).
% 2.42/0.76  fof(f116,plain,(
% 2.42/0.76    spl8_1 <=> v4_ordinal1(sK0)),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.42/0.76  fof(f113,plain,(
% 2.42/0.76    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.42/0.76    inference(equality_resolution,[],[f96])).
% 2.42/0.76  fof(f96,plain,(
% 2.42/0.76    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.42/0.76    inference(cnf_transformation,[],[f63])).
% 2.42/0.76  fof(f63,plain,(
% 2.42/0.76    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.42/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f59,f62,f61,f60])).
% 2.42/0.76  fof(f60,plain,(
% 2.42/0.76    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 2.42/0.76    introduced(choice_axiom,[])).
% 2.42/0.76  fof(f61,plain,(
% 2.42/0.76    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 2.42/0.76    introduced(choice_axiom,[])).
% 2.42/0.76  fof(f62,plain,(
% 2.42/0.76    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 2.42/0.76    introduced(choice_axiom,[])).
% 2.42/0.76  fof(f59,plain,(
% 2.42/0.76    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.42/0.76    inference(rectify,[],[f58])).
% 2.42/0.76  fof(f58,plain,(
% 2.42/0.76    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.42/0.76    inference(nnf_transformation,[],[f3])).
% 2.42/0.76  fof(f3,axiom,(
% 2.42/0.76    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.42/0.76  fof(f650,plain,(
% 2.42/0.76    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f127,f455])).
% 2.42/0.76  fof(f455,plain,(
% 2.42/0.76    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK7(sK0,X7))) ) | ~spl8_1),
% 2.42/0.76    inference(superposition,[],[f114,f408])).
% 2.42/0.76  fof(f114,plain,(
% 2.42/0.76    ( ! [X0,X5] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.42/0.76    inference(equality_resolution,[],[f95])).
% 2.42/0.76  fof(f95,plain,(
% 2.42/0.76    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.42/0.76    inference(cnf_transformation,[],[f63])).
% 2.42/0.76  fof(f1904,plain,(
% 2.42/0.76    ~r1_ordinal1(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f977,f981,f87])).
% 2.42/0.76  fof(f981,plain,(
% 2.42/0.76    ~r1_tarski(sK0,sK7(sK0,sK1)) | (~spl8_1 | ~spl8_3)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f648,f101])).
% 2.42/0.76  fof(f407,plain,(
% 2.42/0.76    spl8_8 | spl8_15 | spl8_1),
% 2.42/0.76    inference(avatar_split_clause,[],[f242,f116,f404,f234])).
% 2.42/0.76  fof(f242,plain,(
% 2.42/0.76    r2_hidden(sK5(sK0,sK0),sK6(sK0,sK0)) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 2.42/0.76    inference(equality_resolution,[],[f152])).
% 2.42/0.76  fof(f152,plain,(
% 2.42/0.76    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(sK0,X0),sK6(sK0,X0)) | r2_hidden(sK5(sK0,X0),X0)) ) | spl8_1),
% 2.42/0.76    inference(superposition,[],[f148,f98])).
% 2.42/0.76  fof(f98,plain,(
% 2.42/0.76    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f63])).
% 2.42/0.76  fof(f148,plain,(
% 2.42/0.76    sK0 != k3_tarski(sK0) | spl8_1),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f118,f78])).
% 2.42/0.76  fof(f78,plain,(
% 2.42/0.76    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 2.42/0.76    inference(cnf_transformation,[],[f44])).
% 2.42/0.76  fof(f118,plain,(
% 2.42/0.76    ~v4_ordinal1(sK0) | spl8_1),
% 2.42/0.76    inference(avatar_component_clause,[],[f116])).
% 2.42/0.76  fof(f398,plain,(
% 2.42/0.76    spl8_1 | ~spl8_5 | ~spl8_8),
% 2.42/0.76    inference(avatar_contradiction_clause,[],[f397])).
% 2.42/0.76  fof(f397,plain,(
% 2.42/0.76    $false | (spl8_1 | ~spl8_5 | ~spl8_8)),
% 2.42/0.76    inference(subsumption_resolution,[],[f396,f267])).
% 2.42/0.76  fof(f267,plain,(
% 2.42/0.76    ~r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (spl8_1 | ~spl8_8)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f148,f104,f236,f100])).
% 2.42/0.76  fof(f100,plain,(
% 2.42/0.76    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f63])).
% 2.42/0.76  fof(f236,plain,(
% 2.42/0.76    r2_hidden(sK5(sK0,sK0),sK0) | ~spl8_8),
% 2.42/0.76    inference(avatar_component_clause,[],[f234])).
% 2.42/0.76  fof(f104,plain,(
% 2.42/0.76    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.42/0.76    inference(definition_unfolding,[],[f69,f70])).
% 2.42/0.76  fof(f69,plain,(
% 2.42/0.76    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.42/0.76    inference(cnf_transformation,[],[f9])).
% 2.42/0.76  fof(f9,axiom,(
% 2.42/0.76    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.42/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.42/0.76  fof(f396,plain,(
% 2.42/0.76    r2_hidden(k2_xboole_0(sK5(sK0,sK0),k1_tarski(sK5(sK0,sK0))),sK0) | (~spl8_5 | ~spl8_8)),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f236,f268,f136])).
% 2.42/0.76  fof(f136,plain,(
% 2.42/0.76    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 2.42/0.76    inference(avatar_component_clause,[],[f135])).
% 2.42/0.76  fof(f135,plain,(
% 2.42/0.76    spl8_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 2.42/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.42/0.76  fof(f268,plain,(
% 2.42/0.76    v3_ordinal1(sK5(sK0,sK0)) | ~spl8_8),
% 2.42/0.76    inference(unit_resulting_resolution,[],[f64,f236,f85])).
% 2.42/0.76  fof(f241,plain,(
% 2.42/0.76    spl8_8 | spl8_9 | spl8_1),
% 2.42/0.76    inference(avatar_split_clause,[],[f232,f116,f238,f234])).
% 2.42/0.76  fof(f232,plain,(
% 2.42/0.76    r2_hidden(sK6(sK0,sK0),sK0) | r2_hidden(sK5(sK0,sK0),sK0) | spl8_1),
% 2.42/0.76    inference(equality_resolution,[],[f153])).
% 2.42/0.76  fof(f153,plain,(
% 2.42/0.76    ( ! [X1] : (sK0 != X1 | r2_hidden(sK6(sK0,X1),sK0) | r2_hidden(sK5(sK0,X1),X1)) ) | spl8_1),
% 2.42/0.76    inference(superposition,[],[f148,f99])).
% 2.42/0.76  fof(f99,plain,(
% 2.42/0.76    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f63])).
% 2.42/0.76  fof(f137,plain,(
% 2.42/0.76    spl8_1 | spl8_5),
% 2.42/0.76    inference(avatar_split_clause,[],[f103,f135,f116])).
% 2.42/0.76  fof(f103,plain,(
% 2.42/0.76    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.42/0.76    inference(definition_unfolding,[],[f65,f70])).
% 2.42/0.76  fof(f65,plain,(
% 2.42/0.76    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.42/0.76    inference(cnf_transformation,[],[f41])).
% 2.42/0.76  fof(f133,plain,(
% 2.42/0.76    ~spl8_1 | spl8_4),
% 2.42/0.76    inference(avatar_split_clause,[],[f66,f130,f116])).
% 2.42/0.76  fof(f66,plain,(
% 2.42/0.76    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.42/0.76    inference(cnf_transformation,[],[f41])).
% 2.42/0.76  fof(f128,plain,(
% 2.42/0.76    ~spl8_1 | spl8_3),
% 2.42/0.76    inference(avatar_split_clause,[],[f67,f125,f116])).
% 2.42/0.76  fof(f67,plain,(
% 2.42/0.76    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 2.42/0.76    inference(cnf_transformation,[],[f41])).
% 2.42/0.76  fof(f123,plain,(
% 2.42/0.76    ~spl8_1 | ~spl8_2),
% 2.42/0.76    inference(avatar_split_clause,[],[f102,f120,f116])).
% 2.42/0.76  fof(f102,plain,(
% 2.42/0.76    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 2.42/0.76    inference(definition_unfolding,[],[f68,f70])).
% 2.42/0.76  fof(f68,plain,(
% 2.42/0.76    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 2.42/0.76    inference(cnf_transformation,[],[f41])).
% 2.42/0.76  % SZS output end Proof for theBenchmark
% 2.42/0.76  % (13448)------------------------------
% 2.42/0.76  % (13448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.76  % (13448)Termination reason: Refutation
% 2.42/0.76  
% 2.42/0.76  % (13448)Memory used [KB]: 12281
% 2.42/0.76  % (13448)Time elapsed: 0.358 s
% 2.42/0.76  % (13448)------------------------------
% 2.42/0.76  % (13448)------------------------------
% 2.83/0.76  % (13421)Success in time 0.4 s
%------------------------------------------------------------------------------
