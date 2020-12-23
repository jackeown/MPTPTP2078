%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:33 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 350 expanded)
%              Number of leaves         :   33 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  566 (1326 expanded)
%              Number of equality atoms :  102 ( 141 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f145,f347,f538,f557,f564,f1057,f1091,f1107])).

fof(f1107,plain,
    ( ~ spl8_4
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f569,f549,f167])).

fof(f167,plain,
    ( spl8_4
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f549,plain,
    ( spl8_19
  <=> r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f569,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ spl8_19 ),
    inference(resolution,[],[f551,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f551,plain,
    ( r2_hidden(sK4,sK3)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1091,plain,
    ( spl8_2
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f1090])).

fof(f1090,plain,
    ( $false
    | spl8_2
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1068,f155])).

fof(f155,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f91,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1068,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl8_2
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f561,f555])).

fof(f555,plain,
    ( sK3 = sK4
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl8_20
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f561,plain,
    ( ~ r1_tarski(sK3,sK4)
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f560,f69])).

fof(f69,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ r1_ordinal1(sK3,sK4)
      | ~ r2_hidden(sK3,k1_ordinal1(sK4)) )
    & ( r1_ordinal1(sK3,sK4)
      | r2_hidden(sK3,k1_ordinal1(sK4)) )
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK3,X1)
            | ~ r2_hidden(sK3,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK3,X1)
            | r2_hidden(sK3,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK3,X1)
          | ~ r2_hidden(sK3,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK3,X1)
          | r2_hidden(sK3,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK3,sK4)
        | ~ r2_hidden(sK3,k1_ordinal1(sK4)) )
      & ( r1_ordinal1(sK3,sK4)
        | r2_hidden(sK3,k1_ordinal1(sK4)) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f560,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ v3_ordinal1(sK3)
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f558,f546])).

fof(f546,plain,
    ( v3_ordinal1(sK4)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f545])).

fof(f545,plain,
    ( spl8_18
  <=> v3_ordinal1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f558,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | spl8_2 ),
    inference(resolution,[],[f143,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f143,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_2
  <=> r1_ordinal1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1057,plain,
    ( spl8_20
    | ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f1056,f167,f137,f553])).

fof(f137,plain,
    ( spl8_1
  <=> r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1056,plain,
    ( sK3 = sK4
    | ~ spl8_1
    | spl8_4 ),
    inference(duplicate_literal_removal,[],[f1055])).

fof(f1055,plain,
    ( sK3 = sK4
    | sK3 = sK4
    | sK3 = sK4
    | sK3 = sK4
    | sK3 = sK4
    | sK3 = sK4
    | ~ spl8_1
    | spl8_4 ),
    inference(resolution,[],[f1050,f110])).

fof(f110,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6)
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP1(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP1(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP1(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP1(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP1(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1050,plain,
    ( sP1(sK3,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_1
    | spl8_4 ),
    inference(resolution,[],[f604,f593])).

fof(f593,plain,
    ( r2_hidden(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_1
    | spl8_4 ),
    inference(resolution,[],[f592,f213])).

fof(f213,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k4_xboole_0(X8,X9))
      | r2_hidden(X7,X8) ) ),
    inference(resolution,[],[f89,f174])).

fof(f174,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f96,f155])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f592,plain,
    ( r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))
    | ~ spl8_1
    | spl8_4 ),
    inference(subsumption_resolution,[],[f590,f169])).

fof(f169,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f167])).

fof(f590,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))
    | ~ spl8_1 ),
    inference(resolution,[],[f576,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f576,plain,
    ( sP0(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4),sK3,sK4)
    | ~ spl8_1 ),
    inference(resolution,[],[f138,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f38,f40])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f138,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f604,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))
      | sP1(X0,X6,X5,X4,X3,X2,X1) ) ),
    inference(resolution,[],[f106,f135])).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP2(X0,X1,X2,X3,X4,X5,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f117,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f117,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP2(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP2(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f39,f43,f42])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP1(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5,X6)
      | ~ r2_hidden(X8,X6)
      | sP1(X8,X5,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ~ sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP1(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).

fof(f63,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ~ sP1(X7,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X7,X6) )
          & ( sP1(X7,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X7,X6) ) )
     => ( ( ~ sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP1(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP1(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP1(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP1(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP1(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ~ sP1(X7,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f564,plain,
    ( spl8_19
    | spl8_2
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f563,f545,f141,f549])).

fof(f563,plain,
    ( r2_hidden(sK4,sK3)
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f562,f69])).

fof(f562,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_ordinal1(sK3)
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f559,f546])).

fof(f559,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | spl8_2 ),
    inference(resolution,[],[f143,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f557,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f70,f545])).

fof(f70,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f538,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f484,f125])).

fof(f125,plain,(
    ! [X0] : r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) ),
    inference(definition_unfolding,[],[f74,f122])).

fof(f122,plain,(
    ! [X0] : k1_ordinal1(X0) = k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) ),
    inference(definition_unfolding,[],[f77,f82,f121])).

fof(f121,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f76,f120])).

fof(f120,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f81,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f95,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(f95,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f81,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f76,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f77,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f484,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK3,k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK3)))
    | spl8_1
    | ~ spl8_2
    | spl8_4 ),
    inference(backward_demodulation,[],[f139,f478])).

fof(f478,plain,
    ( sK3 = sK4
    | ~ spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f477,f70])).

fof(f477,plain,
    ( sK3 = sK4
    | ~ v3_ordinal1(sK4)
    | ~ spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f476,f69])).

fof(f476,plain,
    ( sK3 = sK4
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK4)
    | ~ spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f430,f261])).

fof(f261,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f259,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f259,plain,
    ( r1_tarski(sK3,sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f258,f69])).

fof(f258,plain,
    ( r1_tarski(sK3,sK4)
    | ~ v3_ordinal1(sK3)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f255,f70])).

fof(f255,plain,
    ( r1_tarski(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f87,f142])).

fof(f142,plain,
    ( r1_ordinal1(sK3,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f430,plain,
    ( sK3 = sK4
    | r2_hidden(sK4,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK4)
    | spl8_4 ),
    inference(resolution,[],[f79,f169])).

fof(f79,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f139,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f347,plain,
    ( ~ spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f346,f137,f167])).

fof(f346,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f336,f196])).

fof(f196,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k4_xboole_0(X6,X5))
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f85,f187])).

fof(f187,plain,(
    ! [X2,X1] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(resolution,[],[f97,f155])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f336,plain,
    ( r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))
    | ~ r2_hidden(sK3,sK4)
    | spl8_1 ),
    inference(resolution,[],[f100,f232])).

fof(f232,plain,
    ( ~ sP0(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4),sK3,sK4)
    | spl8_1 ),
    inference(resolution,[],[f103,f139])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f145,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f124,f141,f137])).

fof(f124,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))) ),
    inference(definition_unfolding,[],[f71,f122])).

fof(f71,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f144,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f123,f141,f137])).

fof(f123,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))) ),
    inference(definition_unfolding,[],[f72,f122])).

fof(f72,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (926)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (928)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.49  % (919)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (910)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (911)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (920)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (912)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (927)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (906)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (905)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (909)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (923)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (933)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (922)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (918)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (914)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (903)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (915)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (930)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (929)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (913)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (925)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (921)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (905)Refutation not found, incomplete strategy% (905)------------------------------
% 0.21/0.53  % (905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (905)Memory used [KB]: 10746
% 0.21/0.53  % (905)Time elapsed: 0.112 s
% 0.21/0.53  % (905)------------------------------
% 0.21/0.53  % (905)------------------------------
% 0.21/0.53  % (932)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (917)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (924)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (931)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (914)Refutation not found, incomplete strategy% (914)------------------------------
% 0.21/0.53  % (914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (914)Memory used [KB]: 10746
% 0.21/0.53  % (914)Time elapsed: 0.128 s
% 0.21/0.53  % (914)------------------------------
% 0.21/0.53  % (914)------------------------------
% 0.21/0.53  % (916)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (904)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (915)Refutation not found, incomplete strategy% (915)------------------------------
% 0.21/0.54  % (915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (921)Refutation not found, incomplete strategy% (921)------------------------------
% 1.37/0.54  % (921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (915)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (915)Memory used [KB]: 10746
% 1.37/0.55  % (915)Time elapsed: 0.135 s
% 1.37/0.55  % (915)------------------------------
% 1.37/0.55  % (915)------------------------------
% 1.37/0.55  % (921)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (921)Memory used [KB]: 10618
% 1.37/0.55  % (921)Time elapsed: 0.099 s
% 1.37/0.55  % (921)------------------------------
% 1.37/0.55  % (921)------------------------------
% 1.49/0.59  % (931)Refutation found. Thanks to Tanya!
% 1.49/0.59  % SZS status Theorem for theBenchmark
% 1.49/0.61  % SZS output start Proof for theBenchmark
% 1.49/0.61  fof(f1108,plain,(
% 1.49/0.61    $false),
% 1.49/0.61    inference(avatar_sat_refutation,[],[f144,f145,f347,f538,f557,f564,f1057,f1091,f1107])).
% 1.49/0.61  fof(f1107,plain,(
% 1.49/0.61    ~spl8_4 | ~spl8_19),
% 1.49/0.61    inference(avatar_split_clause,[],[f569,f549,f167])).
% 1.49/0.61  fof(f167,plain,(
% 1.49/0.61    spl8_4 <=> r2_hidden(sK3,sK4)),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.49/0.61  fof(f549,plain,(
% 1.49/0.61    spl8_19 <=> r2_hidden(sK4,sK3)),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.49/0.61  fof(f569,plain,(
% 1.49/0.61    ~r2_hidden(sK3,sK4) | ~spl8_19),
% 1.49/0.61    inference(resolution,[],[f551,f86])).
% 1.49/0.61  fof(f86,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f32])).
% 1.49/0.61  fof(f32,plain,(
% 1.49/0.61    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f1])).
% 1.49/0.61  fof(f1,axiom,(
% 1.49/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.49/0.61  fof(f551,plain,(
% 1.49/0.61    r2_hidden(sK4,sK3) | ~spl8_19),
% 1.49/0.61    inference(avatar_component_clause,[],[f549])).
% 1.49/0.61  fof(f1091,plain,(
% 1.49/0.61    spl8_2 | ~spl8_18 | ~spl8_20),
% 1.49/0.61    inference(avatar_contradiction_clause,[],[f1090])).
% 1.49/0.61  fof(f1090,plain,(
% 1.49/0.61    $false | (spl8_2 | ~spl8_18 | ~spl8_20)),
% 1.49/0.61    inference(subsumption_resolution,[],[f1068,f155])).
% 1.49/0.61  fof(f155,plain,(
% 1.49/0.61    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.49/0.61    inference(duplicate_literal_removal,[],[f154])).
% 1.49/0.61  fof(f154,plain,(
% 1.49/0.61    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.49/0.61    inference(resolution,[],[f91,f90])).
% 1.49/0.61  fof(f90,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f56])).
% 1.49/0.61  fof(f56,plain,(
% 1.49/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).
% 1.49/0.61  fof(f55,plain,(
% 1.49/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f54,plain,(
% 1.49/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.61    inference(rectify,[],[f53])).
% 1.49/0.61  fof(f53,plain,(
% 1.49/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.61    inference(nnf_transformation,[],[f35])).
% 1.49/0.61  fof(f35,plain,(
% 1.49/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.61    inference(ennf_transformation,[],[f2])).
% 1.49/0.61  fof(f2,axiom,(
% 1.49/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.61  fof(f91,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f56])).
% 1.49/0.61  fof(f1068,plain,(
% 1.49/0.61    ~r1_tarski(sK3,sK3) | (spl8_2 | ~spl8_18 | ~spl8_20)),
% 1.49/0.61    inference(backward_demodulation,[],[f561,f555])).
% 1.49/0.61  fof(f555,plain,(
% 1.49/0.61    sK3 = sK4 | ~spl8_20),
% 1.49/0.61    inference(avatar_component_clause,[],[f553])).
% 1.49/0.61  fof(f553,plain,(
% 1.49/0.61    spl8_20 <=> sK3 = sK4),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.49/0.61  fof(f561,plain,(
% 1.49/0.61    ~r1_tarski(sK3,sK4) | (spl8_2 | ~spl8_18)),
% 1.49/0.61    inference(subsumption_resolution,[],[f560,f69])).
% 1.49/0.61  fof(f69,plain,(
% 1.49/0.61    v3_ordinal1(sK3)),
% 1.49/0.61    inference(cnf_transformation,[],[f49])).
% 1.49/0.61  fof(f49,plain,(
% 1.49/0.61    ((~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))) & (r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 1.49/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f48,f47])).
% 1.49/0.61  fof(f47,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK3,X1) | ~r2_hidden(sK3,k1_ordinal1(X1))) & (r1_ordinal1(sK3,X1) | r2_hidden(sK3,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f48,plain,(
% 1.49/0.61    ? [X1] : ((~r1_ordinal1(sK3,X1) | ~r2_hidden(sK3,k1_ordinal1(X1))) & (r1_ordinal1(sK3,X1) | r2_hidden(sK3,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))) & (r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))) & v3_ordinal1(sK4))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f46,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.49/0.61    inference(flattening,[],[f45])).
% 1.49/0.61  fof(f45,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.49/0.61    inference(nnf_transformation,[],[f26])).
% 1.49/0.61  fof(f26,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.49/0.61    inference(ennf_transformation,[],[f24])).
% 1.49/0.61  fof(f24,negated_conjecture,(
% 1.49/0.61    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.49/0.61    inference(negated_conjecture,[],[f23])).
% 1.49/0.61  fof(f23,conjecture,(
% 1.49/0.61    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.49/0.61  fof(f560,plain,(
% 1.49/0.61    ~r1_tarski(sK3,sK4) | ~v3_ordinal1(sK3) | (spl8_2 | ~spl8_18)),
% 1.49/0.61    inference(subsumption_resolution,[],[f558,f546])).
% 1.49/0.61  fof(f546,plain,(
% 1.49/0.61    v3_ordinal1(sK4) | ~spl8_18),
% 1.49/0.61    inference(avatar_component_clause,[],[f545])).
% 1.49/0.61  fof(f545,plain,(
% 1.49/0.61    spl8_18 <=> v3_ordinal1(sK4)),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.49/0.61  fof(f558,plain,(
% 1.49/0.61    ~r1_tarski(sK3,sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK3) | spl8_2),
% 1.49/0.61    inference(resolution,[],[f143,f88])).
% 1.49/0.61  fof(f88,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f52])).
% 1.49/0.61  fof(f52,plain,(
% 1.49/0.61    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.49/0.61    inference(nnf_transformation,[],[f34])).
% 1.49/0.61  fof(f34,plain,(
% 1.49/0.61    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.49/0.61    inference(flattening,[],[f33])).
% 1.49/0.61  fof(f33,plain,(
% 1.49/0.61    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.49/0.61    inference(ennf_transformation,[],[f18])).
% 1.49/0.61  fof(f18,axiom,(
% 1.49/0.61    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.49/0.61  fof(f143,plain,(
% 1.49/0.61    ~r1_ordinal1(sK3,sK4) | spl8_2),
% 1.49/0.61    inference(avatar_component_clause,[],[f141])).
% 1.49/0.61  fof(f141,plain,(
% 1.49/0.61    spl8_2 <=> r1_ordinal1(sK3,sK4)),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.49/0.61  fof(f1057,plain,(
% 1.49/0.61    spl8_20 | ~spl8_1 | spl8_4),
% 1.49/0.61    inference(avatar_split_clause,[],[f1056,f167,f137,f553])).
% 1.49/0.61  fof(f137,plain,(
% 1.49/0.61    spl8_1 <=> r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)))),
% 1.49/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.49/0.61  fof(f1056,plain,(
% 1.49/0.61    sK3 = sK4 | (~spl8_1 | spl8_4)),
% 1.49/0.61    inference(duplicate_literal_removal,[],[f1055])).
% 1.49/0.61  fof(f1055,plain,(
% 1.49/0.61    sK3 = sK4 | sK3 = sK4 | sK3 = sK4 | sK3 = sK4 | sK3 = sK4 | sK3 = sK4 | (~spl8_1 | spl8_4)),
% 1.49/0.61    inference(resolution,[],[f1050,f110])).
% 1.49/0.61  fof(f110,plain,(
% 1.49/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6) | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X1) )),
% 1.49/0.61    inference(cnf_transformation,[],[f67])).
% 1.49/0.61  fof(f67,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.49/0.61    inference(rectify,[],[f66])).
% 1.49/0.61  fof(f66,plain,(
% 1.49/0.61    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP1(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~sP1(X7,X5,X4,X3,X2,X1,X0)))),
% 1.49/0.61    inference(flattening,[],[f65])).
% 1.49/0.61  fof(f65,plain,(
% 1.49/0.61    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP1(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~sP1(X7,X5,X4,X3,X2,X1,X0)))),
% 1.49/0.61    inference(nnf_transformation,[],[f42])).
% 1.49/0.61  fof(f42,plain,(
% 1.49/0.61    ! [X7,X5,X4,X3,X2,X1,X0] : (sP1(X7,X5,X4,X3,X2,X1,X0) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7))),
% 1.49/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.61  fof(f1050,plain,(
% 1.49/0.61    sP1(sK3,sK4,sK4,sK4,sK4,sK4,sK4) | (~spl8_1 | spl8_4)),
% 1.49/0.61    inference(resolution,[],[f604,f593])).
% 1.49/0.61  fof(f593,plain,(
% 1.49/0.61    r2_hidden(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | (~spl8_1 | spl8_4)),
% 1.49/0.61    inference(resolution,[],[f592,f213])).
% 1.49/0.61  fof(f213,plain,(
% 1.49/0.61    ( ! [X8,X7,X9] : (~r2_hidden(X7,k4_xboole_0(X8,X9)) | r2_hidden(X7,X8)) )),
% 1.49/0.61    inference(resolution,[],[f89,f174])).
% 1.49/0.61  fof(f174,plain,(
% 1.49/0.61    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,X2),X1)) )),
% 1.49/0.61    inference(resolution,[],[f96,f155])).
% 1.49/0.61  fof(f96,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f37])).
% 1.49/0.61  fof(f37,plain,(
% 1.49/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.49/0.61    inference(ennf_transformation,[],[f6])).
% 1.49/0.61  fof(f6,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.49/0.61  fof(f89,plain,(
% 1.49/0.61    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f56])).
% 1.49/0.61  fof(f592,plain,(
% 1.49/0.61    r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)) | (~spl8_1 | spl8_4)),
% 1.49/0.61    inference(subsumption_resolution,[],[f590,f169])).
% 1.49/0.61  fof(f169,plain,(
% 1.49/0.61    ~r2_hidden(sK3,sK4) | spl8_4),
% 1.49/0.61    inference(avatar_component_clause,[],[f167])).
% 1.49/0.61  fof(f590,plain,(
% 1.49/0.61    r2_hidden(sK3,sK4) | r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)) | ~spl8_1),
% 1.49/0.61    inference(resolution,[],[f576,f98])).
% 1.49/0.61  fof(f98,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2) | r2_hidden(X1,X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f59])).
% 1.49/0.61  fof(f59,plain,(
% 1.49/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 1.49/0.61    inference(rectify,[],[f58])).
% 1.49/0.61  fof(f58,plain,(
% 1.49/0.61    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 1.49/0.61    inference(nnf_transformation,[],[f40])).
% 1.49/0.61  fof(f40,plain,(
% 1.49/0.61    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.49/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.61  fof(f576,plain,(
% 1.49/0.61    sP0(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4),sK3,sK4) | ~spl8_1),
% 1.49/0.61    inference(resolution,[],[f138,f102])).
% 1.49/0.61  fof(f102,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f60])).
% 1.49/0.61  fof(f60,plain,(
% 1.49/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.49/0.61    inference(nnf_transformation,[],[f41])).
% 1.49/0.61  fof(f41,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 1.49/0.61    inference(definition_folding,[],[f38,f40])).
% 1.49/0.61  fof(f38,plain,(
% 1.49/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.49/0.61    inference(ennf_transformation,[],[f3])).
% 1.49/0.61  fof(f3,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.49/0.61  fof(f138,plain,(
% 1.49/0.61    r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))) | ~spl8_1),
% 1.49/0.61    inference(avatar_component_clause,[],[f137])).
% 1.49/0.61  fof(f604,plain,(
% 1.49/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(X0,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)) | sP1(X0,X6,X5,X4,X3,X2,X1)) )),
% 1.49/0.61    inference(resolution,[],[f106,f135])).
% 1.49/0.61  fof(f135,plain,(
% 1.49/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 1.49/0.61    inference(equality_resolution,[],[f128])).
% 1.49/0.61  fof(f128,plain,(
% 1.49/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 1.49/0.61    inference(definition_unfolding,[],[f117,f105])).
% 1.49/0.61  fof(f105,plain,(
% 1.49/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f14])).
% 1.49/0.61  fof(f14,axiom,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 1.49/0.61  fof(f117,plain,(
% 1.49/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.49/0.61    inference(cnf_transformation,[],[f68])).
% 1.49/0.61  fof(f68,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP2(X0,X1,X2,X3,X4,X5,X6)) & (sP2(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.49/0.61    inference(nnf_transformation,[],[f44])).
% 1.49/0.61  fof(f44,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP2(X0,X1,X2,X3,X4,X5,X6))),
% 1.49/0.61    inference(definition_folding,[],[f39,f43,f42])).
% 1.49/0.61  fof(f43,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : (sP2(X0,X1,X2,X3,X4,X5,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> sP1(X7,X5,X4,X3,X2,X1,X0)))),
% 1.49/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.49/0.61  fof(f39,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.49/0.61    inference(ennf_transformation,[],[f16])).
% 1.49/0.61  fof(f16,axiom,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).
% 1.49/0.61  fof(f106,plain,(
% 1.49/0.61    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5,X6) | ~r2_hidden(X8,X6) | sP1(X8,X5,X4,X3,X2,X1,X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f64])).
% 1.49/0.61  fof(f64,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP2(X0,X1,X2,X3,X4,X5,X6) | ((~sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP1(X8,X5,X4,X3,X2,X1,X0)) & (sP1(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP2(X0,X1,X2,X3,X4,X5,X6)))),
% 1.49/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).
% 1.49/0.61  fof(f63,plain,(
% 1.49/0.61    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : ((~sP1(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP1(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6))) => ((~sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP1(sK7(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f62,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP2(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP1(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP1(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP1(X8,X5,X4,X3,X2,X1,X0)) & (sP1(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP2(X0,X1,X2,X3,X4,X5,X6)))),
% 1.49/0.61    inference(rectify,[],[f61])).
% 1.49/0.61  fof(f61,plain,(
% 1.49/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP2(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP1(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP1(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | ~sP1(X7,X5,X4,X3,X2,X1,X0)) & (sP1(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6))) | ~sP2(X0,X1,X2,X3,X4,X5,X6)))),
% 1.49/0.61    inference(nnf_transformation,[],[f43])).
% 1.49/0.61  fof(f564,plain,(
% 1.49/0.61    spl8_19 | spl8_2 | ~spl8_18),
% 1.49/0.61    inference(avatar_split_clause,[],[f563,f545,f141,f549])).
% 1.49/0.61  fof(f563,plain,(
% 1.49/0.61    r2_hidden(sK4,sK3) | (spl8_2 | ~spl8_18)),
% 1.49/0.61    inference(subsumption_resolution,[],[f562,f69])).
% 1.49/0.61  fof(f562,plain,(
% 1.49/0.61    r2_hidden(sK4,sK3) | ~v3_ordinal1(sK3) | (spl8_2 | ~spl8_18)),
% 1.49/0.61    inference(subsumption_resolution,[],[f559,f546])).
% 1.49/0.61  fof(f559,plain,(
% 1.49/0.61    r2_hidden(sK4,sK3) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK3) | spl8_2),
% 1.49/0.61    inference(resolution,[],[f143,f78])).
% 1.49/0.61  fof(f78,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f28])).
% 1.49/0.61  fof(f28,plain,(
% 1.49/0.61    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.49/0.61    inference(flattening,[],[f27])).
% 1.49/0.61  fof(f27,plain,(
% 1.49/0.61    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.49/0.61    inference(ennf_transformation,[],[f21])).
% 1.49/0.61  fof(f21,axiom,(
% 1.49/0.61    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.49/0.61  fof(f557,plain,(
% 1.49/0.61    spl8_18),
% 1.49/0.61    inference(avatar_split_clause,[],[f70,f545])).
% 1.49/0.61  fof(f70,plain,(
% 1.49/0.61    v3_ordinal1(sK4)),
% 1.49/0.61    inference(cnf_transformation,[],[f49])).
% 1.49/0.61  fof(f538,plain,(
% 1.49/0.61    spl8_1 | ~spl8_2 | spl8_4),
% 1.49/0.61    inference(avatar_contradiction_clause,[],[f533])).
% 1.49/0.61  fof(f533,plain,(
% 1.49/0.61    $false | (spl8_1 | ~spl8_2 | spl8_4)),
% 1.49/0.61    inference(subsumption_resolution,[],[f484,f125])).
% 1.49/0.61  fof(f125,plain,(
% 1.49/0.61    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)))) )),
% 1.49/0.61    inference(definition_unfolding,[],[f74,f122])).
% 1.49/0.61  fof(f122,plain,(
% 1.49/0.61    ( ! [X0] : (k1_ordinal1(X0) = k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) )),
% 1.49/0.61    inference(definition_unfolding,[],[f77,f82,f121])).
% 1.49/0.61  fof(f121,plain,(
% 1.49/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.49/0.61    inference(definition_unfolding,[],[f76,f120])).
% 1.49/0.61  fof(f120,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.49/0.61    inference(definition_unfolding,[],[f81,f119])).
% 1.49/0.61  fof(f119,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.49/0.61    inference(definition_unfolding,[],[f95,f104])).
% 1.49/0.61  fof(f104,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f15])).
% 1.49/0.61  fof(f15,axiom,(
% 1.49/0.61    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).
% 1.49/0.61  fof(f95,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f13])).
% 1.49/0.61  fof(f13,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.49/0.61  fof(f81,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f12])).
% 1.49/0.61  fof(f12,axiom,(
% 1.49/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.61  fof(f76,plain,(
% 1.49/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f11])).
% 1.49/0.61  fof(f11,axiom,(
% 1.49/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.61  fof(f82,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f10])).
% 1.49/0.61  fof(f10,axiom,(
% 1.49/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.49/0.61  fof(f77,plain,(
% 1.49/0.61    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f17])).
% 1.49/0.61  fof(f17,axiom,(
% 1.49/0.61    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.49/0.61  fof(f74,plain,(
% 1.49/0.61    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f19])).
% 1.49/0.61  fof(f19,axiom,(
% 1.49/0.61    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.49/0.61  fof(f484,plain,(
% 1.49/0.61    ~r2_hidden(sK3,k5_xboole_0(sK3,k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK3))) | (spl8_1 | ~spl8_2 | spl8_4)),
% 1.49/0.61    inference(backward_demodulation,[],[f139,f478])).
% 1.49/0.61  fof(f478,plain,(
% 1.49/0.61    sK3 = sK4 | (~spl8_2 | spl8_4)),
% 1.49/0.61    inference(subsumption_resolution,[],[f477,f70])).
% 1.49/0.61  fof(f477,plain,(
% 1.49/0.61    sK3 = sK4 | ~v3_ordinal1(sK4) | (~spl8_2 | spl8_4)),
% 1.49/0.61    inference(subsumption_resolution,[],[f476,f69])).
% 1.49/0.61  fof(f476,plain,(
% 1.49/0.61    sK3 = sK4 | ~v3_ordinal1(sK3) | ~v3_ordinal1(sK4) | (~spl8_2 | spl8_4)),
% 1.49/0.61    inference(subsumption_resolution,[],[f430,f261])).
% 1.49/0.61  fof(f261,plain,(
% 1.49/0.61    ~r2_hidden(sK4,sK3) | ~spl8_2),
% 1.49/0.61    inference(resolution,[],[f259,f94])).
% 1.49/0.61  fof(f94,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f36])).
% 1.49/0.61  fof(f36,plain,(
% 1.49/0.61    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f22])).
% 1.49/0.62  fof(f22,axiom,(
% 1.49/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.49/0.62  fof(f259,plain,(
% 1.49/0.62    r1_tarski(sK3,sK4) | ~spl8_2),
% 1.49/0.62    inference(subsumption_resolution,[],[f258,f69])).
% 1.49/0.62  fof(f258,plain,(
% 1.49/0.62    r1_tarski(sK3,sK4) | ~v3_ordinal1(sK3) | ~spl8_2),
% 1.49/0.62    inference(subsumption_resolution,[],[f255,f70])).
% 1.49/0.62  fof(f255,plain,(
% 1.49/0.62    r1_tarski(sK3,sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK3) | ~spl8_2),
% 1.49/0.62    inference(resolution,[],[f87,f142])).
% 1.49/0.62  fof(f142,plain,(
% 1.49/0.62    r1_ordinal1(sK3,sK4) | ~spl8_2),
% 1.49/0.62    inference(avatar_component_clause,[],[f141])).
% 1.49/0.62  fof(f87,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f52])).
% 1.49/0.62  fof(f430,plain,(
% 1.49/0.62    sK3 = sK4 | r2_hidden(sK4,sK3) | ~v3_ordinal1(sK3) | ~v3_ordinal1(sK4) | spl8_4),
% 1.49/0.62    inference(resolution,[],[f79,f169])).
% 1.49/0.62  fof(f79,plain,(
% 1.49/0.62    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f30])).
% 1.49/0.62  fof(f30,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.49/0.62    inference(flattening,[],[f29])).
% 1.49/0.62  fof(f29,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f20])).
% 1.49/0.62  fof(f20,axiom,(
% 1.49/0.62    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.49/0.62  fof(f139,plain,(
% 1.49/0.62    ~r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4))) | spl8_1),
% 1.49/0.62    inference(avatar_component_clause,[],[f137])).
% 1.49/0.62  fof(f347,plain,(
% 1.49/0.62    ~spl8_4 | spl8_1),
% 1.49/0.62    inference(avatar_split_clause,[],[f346,f137,f167])).
% 1.49/0.62  fof(f346,plain,(
% 1.49/0.62    ~r2_hidden(sK3,sK4) | spl8_1),
% 1.49/0.62    inference(subsumption_resolution,[],[f336,f196])).
% 1.49/0.62  fof(f196,plain,(
% 1.49/0.62    ( ! [X6,X4,X5] : (~r2_hidden(X4,k4_xboole_0(X6,X5)) | ~r2_hidden(X4,X5)) )),
% 1.49/0.62    inference(resolution,[],[f85,f187])).
% 1.49/0.62  fof(f187,plain,(
% 1.49/0.62    ( ! [X2,X1] : (r1_xboole_0(k4_xboole_0(X1,X2),X2)) )),
% 1.49/0.62    inference(resolution,[],[f97,f155])).
% 1.49/0.62  fof(f97,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f37])).
% 1.49/0.62  fof(f85,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f51])).
% 1.49/0.62  fof(f51,plain,(
% 1.49/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.49/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f50])).
% 1.49/0.62  fof(f50,plain,(
% 1.49/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.49/0.62    introduced(choice_axiom,[])).
% 1.49/0.62  fof(f31,plain,(
% 1.49/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.49/0.62    inference(ennf_transformation,[],[f25])).
% 1.49/0.62  fof(f25,plain,(
% 1.49/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.49/0.62    inference(rectify,[],[f4])).
% 1.49/0.62  fof(f4,axiom,(
% 1.49/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.49/0.62  fof(f336,plain,(
% 1.49/0.62    r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)) | ~r2_hidden(sK3,sK4) | spl8_1),
% 1.49/0.62    inference(resolution,[],[f100,f232])).
% 1.49/0.62  fof(f232,plain,(
% 1.49/0.62    ~sP0(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4),sK3,sK4) | spl8_1),
% 1.49/0.62    inference(resolution,[],[f103,f139])).
% 1.49/0.62  fof(f103,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f60])).
% 1.49/0.62  fof(f100,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f59])).
% 1.49/0.62  fof(f145,plain,(
% 1.49/0.62    spl8_1 | spl8_2),
% 1.49/0.62    inference(avatar_split_clause,[],[f124,f141,f137])).
% 1.49/0.62  fof(f124,plain,(
% 1.49/0.62    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)))),
% 1.49/0.62    inference(definition_unfolding,[],[f71,f122])).
% 1.49/0.62  fof(f71,plain,(
% 1.49/0.62    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))),
% 1.49/0.62    inference(cnf_transformation,[],[f49])).
% 1.49/0.62  fof(f144,plain,(
% 1.49/0.62    ~spl8_1 | ~spl8_2),
% 1.49/0.62    inference(avatar_split_clause,[],[f123,f141,f137])).
% 1.49/0.62  fof(f123,plain,(
% 1.49/0.62    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4)))),
% 1.49/0.62    inference(definition_unfolding,[],[f72,f122])).
% 1.49/0.62  fof(f72,plain,(
% 1.49/0.62    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))),
% 1.49/0.62    inference(cnf_transformation,[],[f49])).
% 1.49/0.62  % SZS output end Proof for theBenchmark
% 1.49/0.62  % (931)------------------------------
% 1.49/0.62  % (931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.62  % (931)Termination reason: Refutation
% 1.49/0.62  
% 1.49/0.62  % (931)Memory used [KB]: 6780
% 1.49/0.62  % (931)Time elapsed: 0.194 s
% 1.49/0.62  % (931)------------------------------
% 1.49/0.62  % (931)------------------------------
% 1.49/0.62  % (902)Success in time 0.251 s
%------------------------------------------------------------------------------
