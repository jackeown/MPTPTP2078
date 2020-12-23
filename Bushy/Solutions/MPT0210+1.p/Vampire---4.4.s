%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t136_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:58 EDT 2019

% Result     : Theorem 18.27s
% Output     : Refutation 18.27s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 415 expanded)
%              Number of leaves         :   38 ( 131 expanded)
%              Depth                    :   11
%              Number of atoms          :  673 (1949 expanded)
%              Number of equality atoms :  219 ( 685 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f168,f247,f554,f568,f570,f784,f1024,f1116,f1124,f1135,f1170,f1172,f1248,f1254,f1353,f1355,f1357,f1444,f1450])).

fof(f1450,plain,
    ( spl11_3
    | ~ spl11_46 ),
    inference(avatar_contradiction_clause,[],[f1448])).

fof(f1448,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_46 ),
    inference(resolution,[],[f1404,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',d10_xboole_0)).

fof(f1404,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ spl11_3
    | ~ spl11_46 ),
    inference(backward_demodulation,[],[f1400,f152])).

fof(f152,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl11_3
  <=> ~ r1_tarski(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1400,plain,
    ( sK3 = sK4
    | ~ spl11_46 ),
    inference(resolution,[],[f561,f100])).

fof(f100,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',d1_tarski)).

fof(f561,plain,
    ( r2_hidden(sK4,k1_tarski(sK3))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl11_46
  <=> r2_hidden(sK4,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f1444,plain,
    ( spl11_1
    | ~ spl11_46 ),
    inference(avatar_contradiction_clause,[],[f1442])).

fof(f1442,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_46 ),
    inference(resolution,[],[f1403,f96])).

fof(f1403,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ spl11_1
    | ~ spl11_46 ),
    inference(backward_demodulation,[],[f1400,f146])).

fof(f146,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_1
  <=> ~ r1_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1357,plain,
    ( ~ spl11_9
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f1283,f179,f173])).

fof(f173,plain,
    ( spl11_9
  <=> ~ r1_tarski(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f179,plain,
    ( spl11_11
  <=> ~ r1_tarski(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f1283,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ r1_tarski(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)) ),
    inference(extensionality_resolution,[],[f62,f57])).

fof(f57,plain,(
    k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)) != k2_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)) != k2_tarski(sK4,sK5)
    & sK3 != sK5
    & sK3 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 )
   => ( k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)) != k2_tarski(sK4,sK5)
      & sK3 != sK5
      & sK3 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
      & X0 != X2
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
          & X0 != X2
          & X0 != X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',t136_enumset1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1355,plain,(
    spl11_89 ),
    inference(avatar_contradiction_clause,[],[f1354])).

fof(f1354,plain,
    ( $false
    | ~ spl11_89 ),
    inference(resolution,[],[f1352,f115])).

fof(f115,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f102,f104])).

fof(f104,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f8,f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',d2_tarski)).

fof(f102,plain,(
    ! [X4,X2,X1] :
      ( ~ sP1(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK9(X0,X1,X2) != X0
              & sK9(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sK9(X0,X1,X2) = X0
            | sK9(X0,X1,X2) = X1
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK9(X0,X1,X2) != X0
            & sK9(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sK9(X0,X1,X2) = X0
          | sK9(X0,X1,X2) = X1
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f1352,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK4,sK5))
    | ~ spl11_89 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f1351,plain,
    ( spl11_89
  <=> ~ r2_hidden(sK5,k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f1353,plain,
    ( spl11_8
    | ~ spl11_89
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f1346,f770,f1351,f170])).

fof(f170,plain,
    ( spl11_8
  <=> r1_tarski(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f770,plain,
    ( spl11_50
  <=> sK5 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f1346,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK4,sK5))
    | r1_tarski(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_50 ),
    inference(superposition,[],[f65,f771])).

fof(f771,plain,
    ( sK5 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f770])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',d3_tarski)).

fof(f1254,plain,
    ( spl11_7
    | ~ spl11_84 ),
    inference(avatar_contradiction_clause,[],[f1252])).

fof(f1252,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_84 ),
    inference(resolution,[],[f1178,f96])).

fof(f1178,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ spl11_7
    | ~ spl11_84 ),
    inference(backward_demodulation,[],[f1174,f166])).

fof(f166,plain,
    ( ~ r1_tarski(sK5,sK3)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl11_7
  <=> ~ r1_tarski(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1174,plain,
    ( sK3 = sK5
    | ~ spl11_84 ),
    inference(resolution,[],[f1123,f100])).

fof(f1123,plain,
    ( r2_hidden(sK5,k1_tarski(sK3))
    | ~ spl11_84 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1122,plain,
    ( spl11_84
  <=> r2_hidden(sK5,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f1248,plain,
    ( spl11_5
    | ~ spl11_84 ),
    inference(avatar_contradiction_clause,[],[f1246])).

fof(f1246,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_84 ),
    inference(resolution,[],[f1177,f96])).

fof(f1177,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ spl11_5
    | ~ spl11_84 ),
    inference(backward_demodulation,[],[f1174,f160])).

fof(f160,plain,
    ( ~ r1_tarski(sK3,sK5)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl11_5
  <=> ~ r1_tarski(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1172,plain,(
    spl11_87 ),
    inference(avatar_contradiction_clause,[],[f1171])).

fof(f1171,plain,
    ( $false
    | ~ spl11_87 ),
    inference(resolution,[],[f1169,f116])).

fof(f116,plain,(
    ! [X2,X3] : r2_hidden(X2,k2_tarski(X2,X3)) ),
    inference(resolution,[],[f102,f110])).

fof(f110,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_tarski(X1,X0)) ),
    inference(superposition,[],[f104,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',commutativity_k2_tarski)).

fof(f1169,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK4,sK5))
    | ~ spl11_87 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1168,plain,
    ( spl11_87
  <=> ~ r2_hidden(sK4,k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f1170,plain,
    ( spl11_8
    | ~ spl11_87
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f1163,f776,f1168,f170])).

fof(f776,plain,
    ( spl11_52
  <=> sK4 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f1163,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK4,sK5))
    | r1_tarski(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_52 ),
    inference(superposition,[],[f65,f777])).

fof(f777,plain,
    ( sK4 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f776])).

fof(f1135,plain,
    ( spl11_9
    | ~ spl11_54 ),
    inference(avatar_contradiction_clause,[],[f1134])).

fof(f1134,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_54 ),
    inference(resolution,[],[f1131,f99])).

fof(f99,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1131,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | ~ spl11_9
    | ~ spl11_54 ),
    inference(resolution,[],[f1130,f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f71,f101])).

fof(f101,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f10,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',d5_xboole_0)).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X0)
              & r2_hidden(sK8(X0,X1,X2),X1) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X0)
            & r2_hidden(sK8(X0,X1,X2),X1) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f1130,plain,
    ( r2_hidden(sK3,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_9
    | ~ spl11_54 ),
    inference(forward_demodulation,[],[f1129,f783])).

fof(f783,plain,
    ( sK3 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f782])).

fof(f782,plain,
    ( spl11_54
  <=> sK3 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f1129,plain,
    ( r2_hidden(sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_9 ),
    inference(resolution,[],[f174,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f174,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f1124,plain,
    ( spl11_84
    | ~ spl11_79
    | spl11_83 ),
    inference(avatar_split_clause,[],[f1117,f1114,f1020,f1122])).

fof(f1020,plain,
    ( spl11_79
  <=> ~ r2_hidden(sK5,k1_enumset1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f1114,plain,
    ( spl11_83
  <=> ~ r2_hidden(sK5,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f1117,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK3,sK4,sK5))
    | r2_hidden(sK5,k1_tarski(sK3))
    | ~ spl11_83 ),
    inference(resolution,[],[f1115,f216])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f72,f101])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1115,plain,
    ( ~ r2_hidden(sK5,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_83 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f1116,plain,
    ( spl11_10
    | ~ spl11_83
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f1109,f239,f1114,f176])).

fof(f176,plain,
    ( spl11_10
  <=> r1_tarski(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f239,plain,
    ( spl11_12
  <=> sK5 = sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1109,plain,
    ( ~ r2_hidden(sK5,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | r1_tarski(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_12 ),
    inference(superposition,[],[f65,f240])).

fof(f240,plain,
    ( sK5 = sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f239])).

fof(f1024,plain,(
    spl11_79 ),
    inference(avatar_contradiction_clause,[],[f1023])).

fof(f1023,plain,
    ( $false
    | ~ spl11_79 ),
    inference(resolution,[],[f1021,f131])).

fof(f131,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f108,f105])).

fof(f105,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP2(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ( ( sK10(X0,X1,X2,X3) != X0
              & sK10(X0,X1,X2,X3) != X1
              & sK10(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
          & ( sK10(X0,X1,X2,X3) = X0
            | sK10(X0,X1,X2,X3) = X1
            | sK10(X0,X1,X2,X3) = X2
            | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f51,f52])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK10(X0,X1,X2,X3) != X0
            & sK10(X0,X1,X2,X3) != X1
            & sK10(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
        & ( sK10(X0,X1,X2,X3) = X0
          | sK10(X0,X1,X2,X3) = X1
          | sK10(X0,X1,X2,X3) = X2
          | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP2(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP2(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( sP2(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f108,plain,(
    ! [X2,X0,X1] : sP2(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP2(X2,X1,X0,X3) )
      & ( sP2(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP2(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f18,f23])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t136_enumset1.p',d1_enumset1)).

fof(f1021,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK3,sK4,sK5))
    | ~ spl11_79 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f784,plain,
    ( spl11_50
    | spl11_52
    | spl11_54
    | spl11_9 ),
    inference(avatar_split_clause,[],[f753,f173,f782,f776,f770])).

fof(f753,plain,
    ( sK3 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | sK4 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | sK5 = sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5))
    | ~ spl11_9 ),
    inference(resolution,[],[f494,f203])).

fof(f203,plain,
    ( r2_hidden(sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)),k1_enumset1(sK3,sK4,sK5))
    | ~ spl11_9 ),
    inference(resolution,[],[f202,f190])).

fof(f190,plain,
    ( r2_hidden(sK6(k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)),k2_tarski(sK4,sK5)),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_9 ),
    inference(resolution,[],[f174,f64])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f70,f101])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f494,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f86,f108])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f570,plain,(
    spl11_49 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl11_49 ),
    inference(resolution,[],[f567,f130])).

fof(f130,plain,(
    ! [X4,X5,X3] : r2_hidden(X3,k1_enumset1(X4,X3,X5)) ),
    inference(resolution,[],[f108,f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3] :
      ( ~ sP2(X0,X5,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f567,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(sK3,sK4,sK5))
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl11_49
  <=> ~ r2_hidden(sK4,k1_enumset1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f568,plain,
    ( spl11_46
    | ~ spl11_49
    | spl11_45 ),
    inference(avatar_split_clause,[],[f555,f552,f566,f560])).

fof(f552,plain,
    ( spl11_45
  <=> ~ r2_hidden(sK4,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f555,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(sK3,sK4,sK5))
    | r2_hidden(sK4,k1_tarski(sK3))
    | ~ spl11_45 ),
    inference(resolution,[],[f553,f216])).

fof(f553,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f552])).

fof(f554,plain,
    ( spl11_10
    | ~ spl11_45
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f547,f245,f552,f176])).

fof(f245,plain,
    ( spl11_14
  <=> sK4 = sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f547,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | r1_tarski(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_14 ),
    inference(superposition,[],[f65,f246])).

fof(f246,plain,
    ( sK4 = sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( spl11_12
    | spl11_14
    | spl11_11 ),
    inference(avatar_split_clause,[],[f231,f179,f245,f239])).

fof(f231,plain,
    ( sK4 = sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | sK5 = sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_11 ),
    inference(resolution,[],[f227,f192])).

fof(f192,plain,
    ( r2_hidden(sK6(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3))),k2_tarski(sK4,sK5))
    | ~ spl11_11 ),
    inference(resolution,[],[f180,f64])).

fof(f180,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK5),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_tarski(sK3)))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f78,f104])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f168,plain,
    ( ~ spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f136,f159,f165])).

fof(f136,plain,
    ( ~ r1_tarski(sK3,sK5)
    | ~ r1_tarski(sK5,sK3) ),
    inference(extensionality_resolution,[],[f62,f56])).

fof(f56,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f26])).

fof(f154,plain,
    ( ~ spl11_3
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f134,f145,f151])).

fof(f134,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r1_tarski(sK4,sK3) ),
    inference(extensionality_resolution,[],[f62,f55])).

fof(f55,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
