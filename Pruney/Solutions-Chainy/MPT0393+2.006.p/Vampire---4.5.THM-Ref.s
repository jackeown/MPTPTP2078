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
% DateTime   : Thu Dec  3 12:45:52 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 239 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  402 (1019 expanded)
%              Number of equality atoms :  190 ( 593 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f728,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f179,f184,f267,f493,f557,f562,f571,f618,f726,f727])).

fof(f727,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | sK0 != k3_tarski(k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_tarski(k1_xboole_0))
    | k1_xboole_0 != k3_tarski(k1_xboole_0)
    | r1_tarski(sK0,k1_setfam_1(k1_xboole_0))
    | ~ r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f726,plain,
    ( spl5_4
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f687,f615])).

fof(f615,plain,
    ( ! [X4] : sK0 = X4
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f614])).

fof(f614,plain,
    ( spl5_16
  <=> ! [X4] : sK0 = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f687,plain,
    ( k1_xboole_0 != sK0
    | spl5_4
    | ~ spl5_16 ),
    inference(superposition,[],[f160,f615])).

fof(f160,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_4
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f618,plain,
    ( spl5_16
    | spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f611,f490,f614,f614])).

fof(f490,plain,
    ( spl5_12
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f611,plain,
    ( ! [X6,X7] :
        ( sK0 = X6
        | sK0 = X7 )
    | ~ spl5_12 ),
    inference(resolution,[],[f565,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X0 = X2
      | X1 = X2 ) ),
    inference(superposition,[],[f76,f69])).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f565,plain,
    ( ! [X2] : r2_hidden(sK0,X2)
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f549,f231])).

fof(f231,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f146,f109])).

fof(f109,plain,(
    ! [X4,X5] : r2_hidden(X5,k2_tarski(X4,X5)) ),
    inference(superposition,[],[f71,f69])).

fof(f71,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f146,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,k2_tarski(k1_xboole_0,X11))
      | r1_tarski(k1_xboole_0,X10) ) ),
    inference(resolution,[],[f90,f107])).

fof(f107,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f75,f69])).

fof(f75,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_xboole_0,X1)
      | ~ r2_hidden(X2,X1)
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f549,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,X2)
        | r2_hidden(sK0,X2) )
    | ~ spl5_12 ),
    inference(superposition,[],[f116,f492])).

fof(f492,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f490])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f65,f78])).

fof(f78,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f571,plain,
    ( spl5_11
    | ~ spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f548,f490,f568,f316])).

fof(f316,plain,
    ( spl5_11
  <=> sK0 = k1_setfam_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f568,plain,
    ( spl5_14
  <=> r1_tarski(sK0,k1_setfam_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f548,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k1_xboole_0))
    | sK0 = k1_setfam_1(k1_xboole_0)
    | ~ spl5_12 ),
    inference(superposition,[],[f112,f492])).

fof(f112,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_setfam_1(k1_tarski(X2)))
      | k1_setfam_1(k1_tarski(X2)) = X2 ) ),
    inference(resolution,[],[f57,f87])).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k1_tarski(X0)),X0) ),
    inference(superposition,[],[f62,f64])).

fof(f64,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f562,plain,
    ( spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f543,f490,f559])).

fof(f559,plain,
    ( spl5_13
  <=> sK0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f543,plain,
    ( sK0 = k3_tarski(k1_xboole_0)
    | ~ spl5_12 ),
    inference(superposition,[],[f64,f492])).

fof(f557,plain,
    ( ~ spl5_11
    | spl5_1
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f542,f490,f83,f316])).

fof(f83,plain,
    ( spl5_1
  <=> sK0 = k1_setfam_1(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f542,plain,
    ( sK0 != k1_setfam_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f85,f492])).

fof(f85,plain,
    ( sK0 != k1_setfam_1(k1_tarski(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f493,plain,
    ( spl5_12
    | spl5_1 ),
    inference(avatar_split_clause,[],[f487,f83,f490])).

fof(f487,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f476])).

fof(f476,plain,
    ( sK0 != sK0
    | k1_xboole_0 = k1_tarski(sK0)
    | spl5_1 ),
    inference(superposition,[],[f85,f450])).

fof(f450,plain,(
    ! [X0] :
      ( k1_setfam_1(k1_tarski(X0)) = X0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f436,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f436,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k1_xboole_0
      | ~ r1_tarski(X0,X0)
      | k1_setfam_1(k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f246,f112])).

fof(f246,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(k1_tarski(X0)))
      | k1_tarski(X0) = k1_xboole_0
      | ~ r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k1_tarski(X0) = k1_xboole_0
      | r1_tarski(X1,k1_setfam_1(k1_tarski(X0)))
      | r1_tarski(X1,k1_setfam_1(k1_tarski(X0)))
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f59,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( sK3(k1_tarski(X0),X1) = X0
      | r1_tarski(X1,k1_setfam_1(k1_tarski(X0)))
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f58,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f267,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f260,f264])).

fof(f264,plain,
    ( spl5_9
  <=> k1_xboole_0 = k1_setfam_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f260,plain,(
    k1_xboole_0 = k1_setfam_1(k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f247,f87])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f231,f57])).

fof(f184,plain,
    ( spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f173,f159,f181])).

fof(f181,plain,
    ( spl5_7
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f173,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f64,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f179,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f172,f159,f176])).

fof(f176,plain,
    ( spl5_6
  <=> r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f172,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f87,f161])).

fof(f86,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f42,f83])).

fof(f42,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f23])).

fof(f23,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (26998)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (27004)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (27021)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (27016)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (27008)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (26993)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (26997)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27009)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (26993)Refutation not found, incomplete strategy% (26993)------------------------------
% 0.21/0.51  % (26993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26993)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26993)Memory used [KB]: 1663
% 0.21/0.51  % (26993)Time elapsed: 0.105 s
% 0.21/0.51  % (26993)------------------------------
% 0.21/0.51  % (26993)------------------------------
% 0.21/0.52  % (27013)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (27017)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (26994)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (27004)Refutation not found, incomplete strategy% (27004)------------------------------
% 0.21/0.52  % (27004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26996)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27003)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (27003)Refutation not found, incomplete strategy% (27003)------------------------------
% 0.21/0.52  % (27003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27003)Memory used [KB]: 10618
% 0.21/0.52  % (27003)Time elapsed: 0.127 s
% 0.21/0.52  % (27003)------------------------------
% 0.21/0.52  % (27003)------------------------------
% 0.21/0.52  % (27004)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27004)Memory used [KB]: 10746
% 0.21/0.52  % (27004)Time elapsed: 0.121 s
% 0.21/0.52  % (27004)------------------------------
% 0.21/0.52  % (27004)------------------------------
% 0.21/0.52  % (27005)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (27022)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (26999)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (27019)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (27023)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (27010)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (27020)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (26995)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27018)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (26995)Refutation not found, incomplete strategy% (26995)------------------------------
% 0.21/0.54  % (26995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26995)Memory used [KB]: 10746
% 0.21/0.54  % (26995)Time elapsed: 0.125 s
% 0.21/0.54  % (26995)------------------------------
% 0.21/0.54  % (26995)------------------------------
% 0.21/0.54  % (27012)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (27002)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27015)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (27000)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (27015)Refutation not found, incomplete strategy% (27015)------------------------------
% 0.21/0.54  % (27015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27015)Memory used [KB]: 1663
% 0.21/0.54  % (27015)Time elapsed: 0.140 s
% 0.21/0.54  % (27015)------------------------------
% 0.21/0.54  % (27015)------------------------------
% 0.21/0.54  % (27014)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (27014)Refutation not found, incomplete strategy% (27014)------------------------------
% 1.41/0.55  % (27014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (27014)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (27014)Memory used [KB]: 10746
% 1.41/0.55  % (27014)Time elapsed: 0.142 s
% 1.41/0.55  % (27014)------------------------------
% 1.41/0.55  % (27014)------------------------------
% 1.41/0.55  % (27001)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (27001)Refutation not found, incomplete strategy% (27001)------------------------------
% 1.41/0.55  % (27001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (27001)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (27001)Memory used [KB]: 10618
% 1.41/0.55  % (27001)Time elapsed: 0.151 s
% 1.41/0.55  % (27001)------------------------------
% 1.41/0.55  % (27001)------------------------------
% 1.41/0.55  % (27006)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (27011)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.05/0.66  % (27114)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.25/0.66  % (27115)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.25/0.66  % (27120)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.25/0.67  % (27123)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.25/0.68  % (27122)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.25/0.68  % (27121)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.25/0.68  % (27114)Refutation not found, incomplete strategy% (27114)------------------------------
% 2.25/0.68  % (27114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.68  % (27114)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.68  
% 2.25/0.68  % (27114)Memory used [KB]: 6140
% 2.25/0.68  % (27114)Time elapsed: 0.129 s
% 2.25/0.68  % (27114)------------------------------
% 2.25/0.68  % (27114)------------------------------
% 2.25/0.68  % (27124)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.25/0.72  % (27120)Refutation found. Thanks to Tanya!
% 2.25/0.72  % SZS status Theorem for theBenchmark
% 2.74/0.74  % SZS output start Proof for theBenchmark
% 2.74/0.74  fof(f728,plain,(
% 2.74/0.74    $false),
% 2.74/0.74    inference(avatar_sat_refutation,[],[f86,f179,f184,f267,f493,f557,f562,f571,f618,f726,f727])).
% 2.74/0.74  fof(f727,plain,(
% 2.74/0.74    k1_xboole_0 != k1_tarski(k1_xboole_0) | sK0 != k3_tarski(k1_xboole_0) | k1_xboole_0 != k1_setfam_1(k1_tarski(k1_xboole_0)) | k1_xboole_0 != k3_tarski(k1_xboole_0) | r1_tarski(sK0,k1_setfam_1(k1_xboole_0)) | ~r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)),
% 2.74/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.74/0.74  fof(f726,plain,(
% 2.74/0.74    spl5_4 | ~spl5_16),
% 2.74/0.74    inference(avatar_contradiction_clause,[],[f725])).
% 2.74/0.74  fof(f725,plain,(
% 2.74/0.74    $false | (spl5_4 | ~spl5_16)),
% 2.74/0.74    inference(subsumption_resolution,[],[f687,f615])).
% 2.74/0.74  fof(f615,plain,(
% 2.74/0.74    ( ! [X4] : (sK0 = X4) ) | ~spl5_16),
% 2.74/0.74    inference(avatar_component_clause,[],[f614])).
% 2.74/0.74  fof(f614,plain,(
% 2.74/0.74    spl5_16 <=> ! [X4] : sK0 = X4),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.74/0.74  fof(f687,plain,(
% 2.74/0.74    k1_xboole_0 != sK0 | (spl5_4 | ~spl5_16)),
% 2.74/0.74    inference(superposition,[],[f160,f615])).
% 2.74/0.74  fof(f160,plain,(
% 2.74/0.74    k1_xboole_0 != k1_tarski(k1_xboole_0) | spl5_4),
% 2.74/0.74    inference(avatar_component_clause,[],[f159])).
% 2.74/0.74  fof(f159,plain,(
% 2.74/0.74    spl5_4 <=> k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.74/0.74  fof(f618,plain,(
% 2.74/0.74    spl5_16 | spl5_16 | ~spl5_12),
% 2.74/0.74    inference(avatar_split_clause,[],[f611,f490,f614,f614])).
% 2.74/0.74  fof(f490,plain,(
% 2.74/0.74    spl5_12 <=> k1_xboole_0 = k1_tarski(sK0)),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.74/0.74  fof(f611,plain,(
% 2.74/0.74    ( ! [X6,X7] : (sK0 = X6 | sK0 = X7) ) | ~spl5_12),
% 2.74/0.74    inference(resolution,[],[f565,f137])).
% 2.74/0.74  fof(f137,plain,(
% 2.74/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X1 = X2) )),
% 2.74/0.74    inference(duplicate_literal_removal,[],[f136])).
% 2.74/0.74  fof(f136,plain,(
% 2.74/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X0 = X2 | X1 = X2) )),
% 2.74/0.74    inference(superposition,[],[f76,f69])).
% 2.74/0.74  fof(f69,plain,(
% 2.74/0.74    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.74/0.74    inference(cnf_transformation,[],[f7])).
% 2.74/0.74  fof(f7,axiom,(
% 2.74/0.74    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.74/0.74  fof(f76,plain,(
% 2.74/0.74    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.74/0.74    inference(equality_resolution,[],[f43])).
% 2.74/0.74  fof(f43,plain,(
% 2.74/0.74    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.74/0.74    inference(cnf_transformation,[],[f29])).
% 2.74/0.74  fof(f29,plain,(
% 2.74/0.74    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.74/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 2.74/0.74  fof(f28,plain,(
% 2.74/0.74    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.74/0.74    introduced(choice_axiom,[])).
% 2.74/0.74  fof(f27,plain,(
% 2.74/0.74    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.74/0.74    inference(rectify,[],[f26])).
% 2.74/0.74  fof(f26,plain,(
% 2.74/0.74    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.74/0.74    inference(flattening,[],[f25])).
% 2.74/0.74  fof(f25,plain,(
% 2.74/0.74    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.74/0.74    inference(nnf_transformation,[],[f17])).
% 2.74/0.74  fof(f17,plain,(
% 2.74/0.74    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.74/0.74    inference(ennf_transformation,[],[f4])).
% 2.74/0.74  fof(f4,axiom,(
% 2.74/0.74    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.74/0.74  fof(f565,plain,(
% 2.74/0.74    ( ! [X2] : (r2_hidden(sK0,X2)) ) | ~spl5_12),
% 2.74/0.74    inference(subsumption_resolution,[],[f549,f231])).
% 2.74/0.74  fof(f231,plain,(
% 2.74/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.74/0.74    inference(resolution,[],[f146,f109])).
% 2.74/0.74  fof(f109,plain,(
% 2.74/0.74    ( ! [X4,X5] : (r2_hidden(X5,k2_tarski(X4,X5))) )),
% 2.74/0.74    inference(superposition,[],[f71,f69])).
% 2.74/0.74  fof(f71,plain,(
% 2.74/0.74    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 2.74/0.74    inference(equality_resolution,[],[f70])).
% 2.74/0.74  fof(f70,plain,(
% 2.74/0.74    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 2.74/0.74    inference(equality_resolution,[],[f46])).
% 2.74/0.74  fof(f46,plain,(
% 2.74/0.74    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.74/0.74    inference(cnf_transformation,[],[f29])).
% 2.74/0.74  fof(f146,plain,(
% 2.74/0.74    ( ! [X10,X11] : (~r2_hidden(X10,k2_tarski(k1_xboole_0,X11)) | r1_tarski(k1_xboole_0,X10)) )),
% 2.74/0.74    inference(resolution,[],[f90,f107])).
% 2.74/0.74  fof(f107,plain,(
% 2.74/0.74    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.74/0.74    inference(superposition,[],[f75,f69])).
% 2.74/0.74  fof(f75,plain,(
% 2.74/0.74    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 2.74/0.74    inference(equality_resolution,[],[f74])).
% 2.74/0.74  fof(f74,plain,(
% 2.74/0.74    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 2.74/0.74    inference(equality_resolution,[],[f44])).
% 2.74/0.74  fof(f44,plain,(
% 2.74/0.74    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.74/0.74    inference(cnf_transformation,[],[f29])).
% 2.74/0.74  fof(f90,plain,(
% 2.74/0.74    ( ! [X2,X1] : (~r2_hidden(k1_xboole_0,X1) | ~r2_hidden(X2,X1) | r1_tarski(k1_xboole_0,X2)) )),
% 2.74/0.74    inference(superposition,[],[f60,f61])).
% 2.74/0.74  fof(f61,plain,(
% 2.74/0.74    ( ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0)) )),
% 2.74/0.74    inference(cnf_transformation,[],[f21])).
% 2.74/0.74  fof(f21,plain,(
% 2.74/0.74    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 2.74/0.74    inference(ennf_transformation,[],[f12])).
% 2.74/0.74  fof(f12,axiom,(
% 2.74/0.74    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).
% 2.74/0.74  fof(f60,plain,(
% 2.74/0.74    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 2.74/0.74    inference(cnf_transformation,[],[f20])).
% 2.74/0.74  fof(f20,plain,(
% 2.74/0.74    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 2.74/0.74    inference(ennf_transformation,[],[f11])).
% 2.74/0.74  fof(f11,axiom,(
% 2.74/0.74    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 2.74/0.74  fof(f549,plain,(
% 2.74/0.74    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | r2_hidden(sK0,X2)) ) | ~spl5_12),
% 2.74/0.74    inference(superposition,[],[f116,f492])).
% 2.74/0.74  fof(f492,plain,(
% 2.74/0.74    k1_xboole_0 = k1_tarski(sK0) | ~spl5_12),
% 2.74/0.74    inference(avatar_component_clause,[],[f490])).
% 2.74/0.74  fof(f116,plain,(
% 2.74/0.74    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.74/0.74    inference(resolution,[],[f65,f78])).
% 2.74/0.74  fof(f78,plain,(
% 2.74/0.74    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.74/0.74    inference(equality_resolution,[],[f77])).
% 2.74/0.74  fof(f77,plain,(
% 2.74/0.74    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.74/0.74    inference(equality_resolution,[],[f52])).
% 2.74/0.74  fof(f52,plain,(
% 2.74/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.74/0.74    inference(cnf_transformation,[],[f33])).
% 2.74/0.74  fof(f33,plain,(
% 2.74/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.74/0.74  fof(f32,plain,(
% 2.74/0.74    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.74/0.74    introduced(choice_axiom,[])).
% 2.74/0.74  fof(f31,plain,(
% 2.74/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.74    inference(rectify,[],[f30])).
% 2.74/0.74  fof(f30,plain,(
% 2.74/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.74    inference(nnf_transformation,[],[f5])).
% 2.74/0.74  fof(f5,axiom,(
% 2.74/0.74    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.74/0.74  fof(f65,plain,(
% 2.74/0.74    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.74/0.74    inference(cnf_transformation,[],[f41])).
% 2.74/0.74  fof(f41,plain,(
% 2.74/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 2.74/0.74  fof(f40,plain,(
% 2.74/0.74    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.74/0.74    introduced(choice_axiom,[])).
% 2.74/0.74  fof(f39,plain,(
% 2.74/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/0.74    inference(rectify,[],[f38])).
% 2.74/0.74  fof(f38,plain,(
% 2.74/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/0.74    inference(nnf_transformation,[],[f22])).
% 2.74/0.74  fof(f22,plain,(
% 2.74/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.74/0.74    inference(ennf_transformation,[],[f1])).
% 2.74/0.74  fof(f1,axiom,(
% 2.74/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.74/0.74  fof(f571,plain,(
% 2.74/0.74    spl5_11 | ~spl5_14 | ~spl5_12),
% 2.74/0.74    inference(avatar_split_clause,[],[f548,f490,f568,f316])).
% 2.74/0.74  fof(f316,plain,(
% 2.74/0.74    spl5_11 <=> sK0 = k1_setfam_1(k1_xboole_0)),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.74/0.74  fof(f568,plain,(
% 2.74/0.74    spl5_14 <=> r1_tarski(sK0,k1_setfam_1(k1_xboole_0))),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.74/0.74  fof(f548,plain,(
% 2.74/0.74    ~r1_tarski(sK0,k1_setfam_1(k1_xboole_0)) | sK0 = k1_setfam_1(k1_xboole_0) | ~spl5_12),
% 2.74/0.74    inference(superposition,[],[f112,f492])).
% 2.74/0.74  fof(f112,plain,(
% 2.74/0.74    ( ! [X2] : (~r1_tarski(X2,k1_setfam_1(k1_tarski(X2))) | k1_setfam_1(k1_tarski(X2)) = X2) )),
% 2.74/0.74    inference(resolution,[],[f57,f87])).
% 2.74/0.74  fof(f87,plain,(
% 2.74/0.74    ( ! [X0] : (r1_tarski(k1_setfam_1(k1_tarski(X0)),X0)) )),
% 2.74/0.74    inference(superposition,[],[f62,f64])).
% 2.74/0.74  fof(f64,plain,(
% 2.74/0.74    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.74/0.74    inference(cnf_transformation,[],[f9])).
% 2.74/0.74  fof(f9,axiom,(
% 2.74/0.74    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.74/0.74  fof(f62,plain,(
% 2.74/0.74    ( ! [X0] : (r1_tarski(k1_setfam_1(X0),k3_tarski(X0))) )),
% 2.74/0.74    inference(cnf_transformation,[],[f10])).
% 2.74/0.74  fof(f10,axiom,(
% 2.74/0.74    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).
% 2.74/0.74  fof(f57,plain,(
% 2.74/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.74/0.74    inference(cnf_transformation,[],[f35])).
% 2.74/0.74  fof(f35,plain,(
% 2.74/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.74/0.74    inference(flattening,[],[f34])).
% 2.74/0.74  fof(f34,plain,(
% 2.74/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.74/0.74    inference(nnf_transformation,[],[f3])).
% 2.74/0.74  fof(f3,axiom,(
% 2.74/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.74/0.74  fof(f562,plain,(
% 2.74/0.74    spl5_13 | ~spl5_12),
% 2.74/0.74    inference(avatar_split_clause,[],[f543,f490,f559])).
% 2.74/0.74  fof(f559,plain,(
% 2.74/0.74    spl5_13 <=> sK0 = k3_tarski(k1_xboole_0)),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.74/0.74  fof(f543,plain,(
% 2.74/0.74    sK0 = k3_tarski(k1_xboole_0) | ~spl5_12),
% 2.74/0.74    inference(superposition,[],[f64,f492])).
% 2.74/0.74  fof(f557,plain,(
% 2.74/0.74    ~spl5_11 | spl5_1 | ~spl5_12),
% 2.74/0.74    inference(avatar_split_clause,[],[f542,f490,f83,f316])).
% 2.74/0.74  fof(f83,plain,(
% 2.74/0.74    spl5_1 <=> sK0 = k1_setfam_1(k1_tarski(sK0))),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.74/0.74  fof(f542,plain,(
% 2.74/0.74    sK0 != k1_setfam_1(k1_xboole_0) | (spl5_1 | ~spl5_12)),
% 2.74/0.74    inference(backward_demodulation,[],[f85,f492])).
% 2.74/0.74  fof(f85,plain,(
% 2.74/0.74    sK0 != k1_setfam_1(k1_tarski(sK0)) | spl5_1),
% 2.74/0.74    inference(avatar_component_clause,[],[f83])).
% 2.74/0.74  fof(f493,plain,(
% 2.74/0.74    spl5_12 | spl5_1),
% 2.74/0.74    inference(avatar_split_clause,[],[f487,f83,f490])).
% 2.74/0.74  fof(f487,plain,(
% 2.74/0.74    k1_xboole_0 = k1_tarski(sK0) | spl5_1),
% 2.74/0.74    inference(trivial_inequality_removal,[],[f476])).
% 2.74/0.74  fof(f476,plain,(
% 2.74/0.74    sK0 != sK0 | k1_xboole_0 = k1_tarski(sK0) | spl5_1),
% 2.74/0.74    inference(superposition,[],[f85,f450])).
% 2.74/0.74  fof(f450,plain,(
% 2.74/0.74    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0 | k1_tarski(X0) = k1_xboole_0) )),
% 2.74/0.74    inference(subsumption_resolution,[],[f436,f80])).
% 2.74/0.74  fof(f80,plain,(
% 2.74/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.74/0.74    inference(equality_resolution,[],[f56])).
% 2.74/0.74  fof(f56,plain,(
% 2.74/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.74/0.74    inference(cnf_transformation,[],[f35])).
% 2.74/0.74  fof(f436,plain,(
% 2.74/0.74    ( ! [X0] : (k1_tarski(X0) = k1_xboole_0 | ~r1_tarski(X0,X0) | k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.74/0.74    inference(resolution,[],[f246,f112])).
% 2.74/0.74  fof(f246,plain,(
% 2.74/0.74    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(k1_tarski(X0))) | k1_tarski(X0) = k1_xboole_0 | ~r1_tarski(X1,X0)) )),
% 2.74/0.74    inference(duplicate_literal_removal,[],[f241])).
% 2.74/0.74  fof(f241,plain,(
% 2.74/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_tarski(X0) = k1_xboole_0 | r1_tarski(X1,k1_setfam_1(k1_tarski(X0))) | r1_tarski(X1,k1_setfam_1(k1_tarski(X0))) | k1_tarski(X0) = k1_xboole_0) )),
% 2.74/0.74    inference(superposition,[],[f59,f122])).
% 2.74/0.74  fof(f122,plain,(
% 2.74/0.74    ( ! [X0,X1] : (sK3(k1_tarski(X0),X1) = X0 | r1_tarski(X1,k1_setfam_1(k1_tarski(X0))) | k1_tarski(X0) = k1_xboole_0) )),
% 2.74/0.74    inference(resolution,[],[f58,f79])).
% 2.74/0.74  fof(f79,plain,(
% 2.74/0.74    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.74/0.74    inference(equality_resolution,[],[f51])).
% 2.74/0.74  fof(f51,plain,(
% 2.74/0.74    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.74/0.74    inference(cnf_transformation,[],[f33])).
% 2.74/0.74  fof(f58,plain,(
% 2.74/0.74    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.74/0.74    inference(cnf_transformation,[],[f37])).
% 2.74/0.74  fof(f37,plain,(
% 2.74/0.74    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 2.74/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f36])).
% 2.74/0.74  fof(f36,plain,(
% 2.74/0.74    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 2.74/0.74    introduced(choice_axiom,[])).
% 2.74/0.74  fof(f19,plain,(
% 2.74/0.74    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.74/0.74    inference(flattening,[],[f18])).
% 2.74/0.74  fof(f18,plain,(
% 2.74/0.74    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.74/0.74    inference(ennf_transformation,[],[f13])).
% 2.74/0.74  fof(f13,axiom,(
% 2.74/0.74    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.74/0.74  fof(f59,plain,(
% 2.74/0.74    ( ! [X0,X1] : (~r1_tarski(X1,sK3(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.74/0.74    inference(cnf_transformation,[],[f37])).
% 2.74/0.74  fof(f267,plain,(
% 2.74/0.74    spl5_9),
% 2.74/0.74    inference(avatar_split_clause,[],[f260,f264])).
% 2.74/0.74  fof(f264,plain,(
% 2.74/0.74    spl5_9 <=> k1_xboole_0 = k1_setfam_1(k1_tarski(k1_xboole_0))),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.74/0.74  fof(f260,plain,(
% 2.74/0.74    k1_xboole_0 = k1_setfam_1(k1_tarski(k1_xboole_0))),
% 2.74/0.74    inference(resolution,[],[f247,f87])).
% 2.74/0.74  fof(f247,plain,(
% 2.74/0.74    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.74/0.74    inference(resolution,[],[f231,f57])).
% 2.74/0.74  fof(f184,plain,(
% 2.74/0.74    spl5_7 | ~spl5_4),
% 2.74/0.74    inference(avatar_split_clause,[],[f173,f159,f181])).
% 2.74/0.74  fof(f181,plain,(
% 2.74/0.74    spl5_7 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.74/0.74  fof(f173,plain,(
% 2.74/0.74    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl5_4),
% 2.74/0.74    inference(superposition,[],[f64,f161])).
% 2.74/0.74  fof(f161,plain,(
% 2.74/0.74    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl5_4),
% 2.74/0.74    inference(avatar_component_clause,[],[f159])).
% 2.74/0.74  fof(f179,plain,(
% 2.74/0.74    spl5_6 | ~spl5_4),
% 2.74/0.74    inference(avatar_split_clause,[],[f172,f159,f176])).
% 2.74/0.74  fof(f176,plain,(
% 2.74/0.74    spl5_6 <=> r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)),
% 2.74/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.74/0.74  fof(f172,plain,(
% 2.74/0.74    r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 2.74/0.74    inference(superposition,[],[f87,f161])).
% 2.74/0.74  fof(f86,plain,(
% 2.74/0.74    ~spl5_1),
% 2.74/0.74    inference(avatar_split_clause,[],[f42,f83])).
% 2.74/0.74  fof(f42,plain,(
% 2.74/0.74    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.74/0.74    inference(cnf_transformation,[],[f24])).
% 2.74/0.74  fof(f24,plain,(
% 2.74/0.74    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.74/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f23])).
% 2.74/0.74  fof(f23,plain,(
% 2.74/0.74    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.74/0.74    introduced(choice_axiom,[])).
% 2.74/0.74  fof(f16,plain,(
% 2.74/0.74    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.74/0.74    inference(ennf_transformation,[],[f15])).
% 2.74/0.74  fof(f15,negated_conjecture,(
% 2.74/0.74    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.74/0.74    inference(negated_conjecture,[],[f14])).
% 2.74/0.74  fof(f14,conjecture,(
% 2.74/0.74    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.74/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.74/0.74  % SZS output end Proof for theBenchmark
% 2.74/0.74  % (27120)------------------------------
% 2.74/0.74  % (27120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.74/0.74  % (27120)Termination reason: Refutation
% 2.74/0.74  
% 2.74/0.74  % (27120)Memory used [KB]: 6652
% 2.74/0.74  % (27120)Time elapsed: 0.157 s
% 2.74/0.74  % (27120)------------------------------
% 2.74/0.74  % (27120)------------------------------
% 2.74/0.74  % (26989)Success in time 0.375 s
%------------------------------------------------------------------------------
