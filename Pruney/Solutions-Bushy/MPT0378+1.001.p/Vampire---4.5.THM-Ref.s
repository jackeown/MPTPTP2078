%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0378+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:52 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 214 expanded)
%              Number of leaves         :   42 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  535 (1361 expanded)
%              Number of equality atoms :  204 ( 325 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f224,f309,f393,f426,f431,f474,f1282,f1284,f1285,f1286,f1287,f1288,f1289])).

fof(f1289,plain,
    ( sK6 != sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ m1_subset_1(sK6,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1288,plain,
    ( sK5 != sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ m1_subset_1(sK5,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1287,plain,
    ( sK4 != sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ m1_subset_1(sK4,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1286,plain,
    ( sK3 != sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ m1_subset_1(sK3,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1285,plain,
    ( sK2 != sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1284,plain,
    ( sK1 != sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1282,plain,
    ( spl10_25
    | spl10_26
    | spl10_27
    | spl10_28
    | spl10_29
    | spl10_30
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f1245,f428,f1279,f1275,f1271,f1267,f1263,f1259])).

fof(f1259,plain,
    ( spl10_25
  <=> sK1 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f1263,plain,
    ( spl10_26
  <=> sK2 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f1267,plain,
    ( spl10_27
  <=> sK3 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f1271,plain,
    ( spl10_28
  <=> sK4 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f1275,plain,
    ( spl10_29
  <=> sK5 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f1279,plain,
    ( spl10_30
  <=> sK6 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f428,plain,
    ( spl10_23
  <=> r2_hidden(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f1245,plain,
    ( sK6 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK5 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK4 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK3 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK2 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK1 = sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl10_23 ),
    inference(resolution,[],[f430,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X8,X5,X3,X1] :
      ( X5 = X8
      | X4 = X8
      | X3 = X8
      | X2 = X8
      | X1 = X8
      | X0 = X8
      | ~ r2_hidden(X8,k4_enumset1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( X5 = X8
      | X4 = X8
      | X3 = X8
      | X2 = X8
      | X1 = X8
      | X0 = X8
      | ~ r2_hidden(X8,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ( ( ( sK9(X0,X1,X2,X3,X4,X5,X6) != X5
              & sK9(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK9(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK9(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK9(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK9(X0,X1,X2,X3,X4,X5,X6) != X0 )
            | ~ r2_hidden(sK9(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK9(X0,X1,X2,X3,X4,X5,X6) = X5
            | sK9(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK9(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK9(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK9(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK9(X0,X1,X2,X3,X4,X5,X6) = X0
            | r2_hidden(sK9(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).

fof(f35,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK9(X0,X1,X2,X3,X4,X5,X6) != X5
            & sK9(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK9(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK9(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK9(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK9(X0,X1,X2,X3,X4,X5,X6) != X0 )
          | ~ r2_hidden(sK9(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK9(X0,X1,X2,X3,X4,X5,X6) = X5
          | sK9(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK9(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK9(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK9(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK9(X0,X1,X2,X3,X4,X5,X6) = X0
          | r2_hidden(sK9(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
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
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
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
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f430,plain,
    ( r2_hidden(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f428])).

fof(f474,plain,
    ( ~ spl10_24
    | spl10_11
    | spl10_22 ),
    inference(avatar_split_clause,[],[f460,f423,f221,f471])).

fof(f471,plain,
    ( spl10_24
  <=> m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f221,plain,
    ( spl10_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f423,plain,
    ( spl10_22
  <=> r2_hidden(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f460,plain,
    ( ~ m1_subset_1(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | spl10_11
    | spl10_22 ),
    inference(unit_resulting_resolution,[],[f223,f425,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f425,plain,
    ( ~ r2_hidden(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f423])).

fof(f223,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f221])).

fof(f431,plain,
    ( spl10_23
    | spl10_21 ),
    inference(avatar_split_clause,[],[f410,f389,f428])).

fof(f389,plain,
    ( spl10_21
  <=> r1_tarski(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f410,plain,
    ( r2_hidden(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f391,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f391,plain,
    ( ~ r1_tarski(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f389])).

fof(f426,plain,
    ( ~ spl10_22
    | spl10_21 ),
    inference(avatar_split_clause,[],[f411,f389,f423])).

fof(f411,plain,
    ( ~ r2_hidden(sK7(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f391,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f393,plain,
    ( ~ spl10_21
    | spl10_18 ),
    inference(avatar_split_clause,[],[f376,f306,f389])).

fof(f306,plain,
    ( spl10_18
  <=> r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f376,plain,
    ( ~ r1_tarski(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | spl10_18 ),
    inference(resolution,[],[f308,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK8(X0,X1),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r1_tarski(sK8(X0,X1),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK8(X0,X1),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( r1_tarski(sK8(X0,X1),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f308,plain,
    ( ~ r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f306])).

fof(f309,plain,
    ( ~ spl10_18
    | spl10_1 ),
    inference(avatar_split_clause,[],[f304,f88,f306])).

fof(f88,plain,
    ( spl10_1
  <=> m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f304,plain,
    ( ~ r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f293,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f293,plain,
    ( ~ r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl10_1 ),
    inference(resolution,[],[f90,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,
    ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f224,plain,
    ( ~ spl10_11
    | spl10_2 ),
    inference(avatar_split_clause,[],[f127,f93,f221])).

fof(f93,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f127,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f95,plain,
    ( k1_xboole_0 != sK0
    | spl10_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f126,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f37,f123])).

fof(f123,plain,
    ( spl10_8
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f37,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK6,sK0)
    & m1_subset_1(sK5,sK0)
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f21,f20,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(sK1,X2,X3,X4,X5,X6),k1_zfmisc_1(sK0))
                          & k1_xboole_0 != sK0
                          & m1_subset_1(X6,sK0) )
                      & m1_subset_1(X5,sK0) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ m1_subset_1(k4_enumset1(sK1,X2,X3,X4,X5,X6),k1_zfmisc_1(sK0))
                        & k1_xboole_0 != sK0
                        & m1_subset_1(X6,sK0) )
                    & m1_subset_1(X5,sK0) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ m1_subset_1(k4_enumset1(sK1,sK2,X3,X4,X5,X6),k1_zfmisc_1(sK0))
                      & k1_xboole_0 != sK0
                      & m1_subset_1(X6,sK0) )
                  & m1_subset_1(X5,sK0) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ m1_subset_1(k4_enumset1(sK1,sK2,X3,X4,X5,X6),k1_zfmisc_1(sK0))
                    & k1_xboole_0 != sK0
                    & m1_subset_1(X6,sK0) )
                & m1_subset_1(X5,sK0) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,sK0) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,X4,X5,X6),k1_zfmisc_1(sK0))
                  & k1_xboole_0 != sK0
                  & m1_subset_1(X6,sK0) )
              & m1_subset_1(X5,sK0) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,X4,X5,X6),k1_zfmisc_1(sK0))
                & k1_xboole_0 != sK0
                & m1_subset_1(X6,sK0) )
            & m1_subset_1(X5,sK0) )
        & m1_subset_1(X4,sK0) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,X5,X6),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X6,sK0) )
          & m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,X5,X6),k1_zfmisc_1(sK0))
            & k1_xboole_0 != sK0
            & m1_subset_1(X6,sK0) )
        & m1_subset_1(X5,sK0) )
   => ( ? [X6] :
          ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,X6),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X6] :
        ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,X6),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X6,sK0) )
   => ( ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK6,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

fof(f121,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f38,f118])).

fof(f118,plain,
    ( spl10_7
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f38,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f39,f113])).

fof(f113,plain,
    ( spl10_6
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f39,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f108,plain,
    ( spl10_5
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f40,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f41,f103])).

fof(f103,plain,
    ( spl10_4
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f41,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f42,f98])).

fof(f98,plain,
    ( spl10_3
  <=> m1_subset_1(sK6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f42,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f43,f93])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
