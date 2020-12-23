%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 131 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 (1195 expanded)
%              Number of equality atoms :  314 (1048 expanded)
%              Maximal formula depth    :   25 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f133,f189,f198])).

fof(f198,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f19,f104])).

fof(f104,plain,
    ( ! [X5] : sK2 = X5
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_1
  <=> ! [X5] : sK2 = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f19,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f189,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f19,f132])).

fof(f132,plain,
    ( ! [X5] : sK1 = X5
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_3
  <=> ! [X5] : sK1 = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f133,plain,
    ( spl4_3
    | spl4_3
    | spl4_3
    | spl4_3
    | spl4_3
    | spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f129,f106,f131,f131,f131,f131,f131,f131])).

fof(f106,plain,
    ( spl4_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f129,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( sK1 = X0
        | sK1 = X1
        | sK1 = X2
        | sK1 = X3
        | sK1 = X4
        | sK1 = X5 )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f128,f114])).

fof(f114,plain,
    ( sK0 != sK1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f19,f108])).

fof(f108,plain,
    ( sK0 = sK2
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK0 = sK1
      | sK1 = X5 ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK0 = sK1
      | sK0 = sK1
      | sK0 = sK1
      | sK1 = X5 ) ),
    inference(resolution,[],[f95,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] :
      ( ~ r2_hidden(X11,k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)))
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | X8 = X11 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 = X11
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | ~ r2_hidden(X11,X9)
      | k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9 ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 = X11
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | ~ r2_hidden(X11,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 )
            | ~ r2_hidden(X10,X9) )
          & ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10
            | r2_hidden(X10,X9) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f95,plain,(
    ! [X47,X45,X43,X46,X44,X42] : r2_hidden(sK1,k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_enumset1(X42,X43,X44,X45,X46,X47))) ),
    inference(superposition,[],[f84,f47])).

fof(f47,plain,(
    k1_enumset1(sK0,sK0,sK0) = k1_enumset1(sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f18,f46,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11] : r2_hidden(X11,k2_xboole_0(k1_enumset1(X0,X11,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] :
      ( r2_hidden(X11,X9)
      | k2_xboole_0(k1_enumset1(X0,X11,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9 ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( spl4_1
    | spl4_2
    | spl4_1
    | spl4_1
    | spl4_1
    | spl4_1
    | spl4_1 ),
    inference(avatar_split_clause,[],[f101,f103,f103,f103,f103,f103,f106,f103])).

% (11593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK2 = X0
      | sK2 = X1
      | sK2 = X2
      | sK2 = X3
      | sK2 = X4
      | sK0 = sK2
      | sK2 = X5 ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK2 = X0
      | sK2 = X1
      | sK2 = X2
      | sK2 = X3
      | sK2 = X4
      | sK0 = sK2
      | sK0 = sK2
      | sK0 = sK2
      | sK2 = X5 ) ),
    inference(resolution,[],[f94,f87])).

fof(f94,plain,(
    ! [X39,X37,X41,X38,X36,X40] : r2_hidden(sK2,k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_enumset1(X36,X37,X38,X39,X40,X41))) ),
    inference(superposition,[],[f82,f47])).

fof(f82,plain,(
    ! [X6,X4,X0,X8,X7,X5,X3,X1,X11] : r2_hidden(X11,k2_xboole_0(k1_enumset1(X0,X1,X11),k4_enumset1(X3,X4,X5,X6,X7,X8))) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X4,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | k2_xboole_0(k1_enumset1(X0,X1,X11),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X2 != X11
      | k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9 ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X2 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (11591)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (11584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (11590)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (11585)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11586)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (11588)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11587)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11599)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (11592)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (11591)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (11600)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (11592)Refutation not found, incomplete strategy% (11592)------------------------------
% 0.21/0.52  % (11592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11600)Refutation not found, incomplete strategy% (11600)------------------------------
% 0.21/0.52  % (11600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11592)Memory used [KB]: 10618
% 0.21/0.52  % (11592)Time elapsed: 0.098 s
% 0.21/0.52  % (11592)------------------------------
% 0.21/0.52  % (11592)------------------------------
% 0.21/0.52  % (11600)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11600)Memory used [KB]: 10618
% 0.21/0.52  % (11600)Time elapsed: 0.105 s
% 0.21/0.52  % (11600)------------------------------
% 0.21/0.52  % (11600)------------------------------
% 0.21/0.53  % (11583)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11608)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (11583)Refutation not found, incomplete strategy% (11583)------------------------------
% 0.21/0.53  % (11583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11583)Memory used [KB]: 1663
% 0.21/0.53  % (11583)Time elapsed: 0.118 s
% 0.21/0.53  % (11583)------------------------------
% 0.21/0.53  % (11583)------------------------------
% 0.21/0.53  % (11595)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11606)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (11606)Refutation not found, incomplete strategy% (11606)------------------------------
% 0.21/0.53  % (11606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11606)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11606)Memory used [KB]: 1791
% 0.21/0.53  % (11606)Time elapsed: 0.092 s
% 0.21/0.53  % (11606)------------------------------
% 0.21/0.53  % (11606)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f109,f133,f189,f198])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~spl4_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    $false | ~spl4_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f19,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X5] : (sK2 = X5) ) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl4_1 <=> ! [X5] : sK2 = X5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    sK1 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~spl4_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    $false | ~spl4_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f19,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X5] : (sK1 = X5) ) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl4_3 <=> ! [X5] : sK1 = X5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl4_3 | spl4_3 | spl4_3 | spl4_3 | spl4_3 | spl4_3 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f129,f106,f131,f131,f131,f131,f131,f131])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl4_2 <=> sK0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK1 = X5) ) | ~spl4_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    sK0 != sK1 | ~spl4_2),
% 0.21/0.53    inference(backward_demodulation,[],[f19,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    sK0 = sK2 | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK0 = sK1 | sK1 = X5) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK1 = X5) )),
% 0.21/0.53    inference(resolution,[],[f95,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] : (~r2_hidden(X11,k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | X8 = X11) )),
% 0.21/0.53    inference(equality_resolution,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9) | k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9))) => (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(rectify,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X47,X45,X43,X46,X44,X42] : (r2_hidden(sK1,k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_enumset1(X42,X43,X44,X45,X46,X47)))) )),
% 0.21/0.53    inference(superposition,[],[f84,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK0,sK0) = k1_enumset1(sK1,sK1,sK2)),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f46,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f22])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11] : (r2_hidden(X11,k2_xboole_0(k1_enumset1(X0,X11,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] : (r2_hidden(X11,X9) | k2_xboole_0(k1_enumset1(X0,X11,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9) )),
% 0.21/0.53    inference(equality_resolution,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f24])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl4_1 | spl4_2 | spl4_1 | spl4_1 | spl4_1 | spl4_1 | spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f101,f103,f103,f103,f103,f103,f106,f103])).
% 0.21/0.53  % (11593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK2 = X0 | sK2 = X1 | sK2 = X2 | sK2 = X3 | sK2 = X4 | sK0 = sK2 | sK2 = X5) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sK2 = X0 | sK2 = X1 | sK2 = X2 | sK2 = X3 | sK2 = X4 | sK0 = sK2 | sK0 = sK2 | sK0 = sK2 | sK2 = X5) )),
% 0.21/0.53    inference(resolution,[],[f94,f87])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X39,X37,X41,X38,X36,X40] : (r2_hidden(sK2,k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_enumset1(X36,X37,X38,X39,X40,X41)))) )),
% 0.21/0.53    inference(superposition,[],[f82,f47])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X6,X4,X0,X8,X7,X5,X3,X1,X11] : (r2_hidden(X11,k2_xboole_0(k1_enumset1(X0,X1,X11),k4_enumset1(X3,X4,X5,X6,X7,X8)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X6,X4,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | k2_xboole_0(k1_enumset1(X0,X1,X11),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9) )),
% 0.21/0.53    inference(equality_resolution,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X2 != X11 | k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != X9) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f24])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X2 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11591)------------------------------
% 0.21/0.53  % (11591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11591)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11591)Memory used [KB]: 10746
% 0.21/0.53  % (11591)Time elapsed: 0.116 s
% 0.21/0.53  % (11591)------------------------------
% 0.21/0.53  % (11591)------------------------------
% 0.21/0.53  % (11596)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (11582)Success in time 0.17 s
%------------------------------------------------------------------------------
