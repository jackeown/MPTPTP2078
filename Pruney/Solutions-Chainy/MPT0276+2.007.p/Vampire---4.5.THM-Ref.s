%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:29 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 505 expanded)
%              Number of leaves         :   45 ( 193 expanded)
%              Depth                    :   12
%              Number of atoms          :  613 (2331 expanded)
%              Number of equality atoms :  191 ( 890 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f223,f233,f271,f281,f291,f308,f318,f338,f344,f354,f393,f397,f408,f486,f590,f591,f592,f595,f597,f598,f746,f751,f752,f772,f777,f778,f781,f782,f783,f785,f786])).

fof(f786,plain,
    ( spl5_26
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f346,f274,f348])).

fof(f348,plain,
    ( spl5_26
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f274,plain,
    ( spl5_14
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f346,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f276,f86])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f276,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f274])).

fof(f785,plain,
    ( ~ spl5_9
    | spl5_13
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f519,f315,f268,f145])).

fof(f145,plain,
    ( spl5_9
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f268,plain,
    ( spl5_13
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f315,plain,
    ( spl5_22
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f519,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_13
    | ~ spl5_22 ),
    inference(superposition,[],[f270,f317])).

fof(f317,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f315])).

fof(f270,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f268])).

fof(f783,plain,
    ( spl5_40
    | ~ spl5_25
    | spl5_28 ),
    inference(avatar_split_clause,[],[f740,f390,f341,f742])).

fof(f742,plain,
    ( spl5_40
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f341,plain,
    ( spl5_25
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f390,plain,
    ( spl5_28
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f740,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | ~ spl5_25
    | spl5_28 ),
    inference(subsumption_resolution,[],[f739,f391])).

fof(f391,plain,
    ( sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f390])).

fof(f739,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | ~ spl5_25 ),
    inference(resolution,[],[f343,f86])).

fof(f343,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f341])).

fof(f782,plain,
    ( spl5_10
    | ~ spl5_19
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f546,f479,f298,f149])).

fof(f149,plain,
    ( spl5_10
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f298,plain,
    ( spl5_19
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f479,plain,
    ( spl5_32
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f546,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_19
    | ~ spl5_32 ),
    inference(superposition,[],[f299,f481])).

fof(f481,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f479])).

fof(f299,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f298])).

fof(f781,plain,
    ( ~ spl5_14
    | spl5_3
    | spl5_15
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f780,f335,f278,f98,f274])).

fof(f98,plain,
    ( spl5_3
  <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f278,plain,
    ( spl5_15
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f335,plain,
    ( spl5_24
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f780,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_3
    | spl5_15
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f779,f337])).

fof(f337,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f335])).

fof(f779,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_3
    | spl5_15 ),
    inference(subsumption_resolution,[],[f394,f280])).

fof(f280,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f278])).

fof(f394,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f202])).

fof(f202,plain,
    ( ! [X0] :
        ( k1_enumset1(sK0,sK0,sK0) != X0
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),sK2)
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),k1_enumset1(sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f100,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f100,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK0,sK0,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f778,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f777,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f772,plain,
    ( spl5_16
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | spl5_16
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f756,f83])).

fof(f83,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f35])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f756,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1))
    | spl5_16
    | ~ spl5_28 ),
    inference(superposition,[],[f285,f392])).

fof(f392,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f390])).

fof(f285,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl5_16
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f752,plain,
    ( sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f751,plain,
    ( sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f746,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f598,plain,
    ( ~ spl5_10
    | spl5_13
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f321,f311,f268,f149])).

fof(f311,plain,
    ( spl5_21
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f321,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_13
    | ~ spl5_21 ),
    inference(superposition,[],[f270,f313])).

fof(f313,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f311])).

fof(f597,plain,
    ( spl5_36
    | ~ spl5_24
    | spl5_26 ),
    inference(avatar_split_clause,[],[f561,f348,f335,f563])).

fof(f563,plain,
    ( spl5_36
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f561,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_24
    | spl5_26 ),
    inference(subsumption_resolution,[],[f560,f349])).

fof(f349,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f348])).

fof(f560,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_24 ),
    inference(resolution,[],[f337,f86])).

fof(f595,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f592,plain,
    ( sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f591,plain,
    ( sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f590,plain,
    ( spl5_14
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | spl5_14
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f578,f83])).

fof(f578,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl5_14
    | ~ spl5_26 ),
    inference(superposition,[],[f275,f350])).

fof(f350,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f348])).

fof(f275,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f274])).

fof(f486,plain,
    ( spl5_32
    | spl5_33
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f477,f294,f483,f479])).

fof(f483,plain,
    ( spl5_33
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f294,plain,
    ( spl5_18
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f477,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_18 ),
    inference(resolution,[],[f296,f86])).

fof(f296,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f294])).

fof(f408,plain,
    ( ~ spl5_18
    | spl5_19
    | spl5_1 ),
    inference(avatar_split_clause,[],[f405,f88,f298,f294])).

fof(f88,plain,
    ( spl5_1
  <=> k1_enumset1(sK0,sK0,sK1) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f405,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,
    ( ! [X2] :
        ( k1_enumset1(sK0,sK0,sK1) != X2
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),sK2)
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),k1_enumset1(sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),X2) )
    | spl5_1 ),
    inference(superposition,[],[f90,f64])).

fof(f90,plain,
    ( k1_enumset1(sK0,sK0,sK1) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f397,plain,
    ( ~ spl5_16
    | ~ spl5_25
    | spl5_2
    | spl5_17 ),
    inference(avatar_split_clause,[],[f396,f288,f93,f341,f284])).

fof(f93,plain,
    ( spl5_2
  <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f288,plain,
    ( spl5_17
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f396,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))
    | spl5_2
    | spl5_17 ),
    inference(subsumption_resolution,[],[f395,f290])).

fof(f290,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f288])).

fof(f395,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f203])).

fof(f203,plain,
    ( ! [X1] :
        ( k1_enumset1(sK1,sK1,sK1) != X1
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),sK2)
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),k1_enumset1(sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),X1) )
    | spl5_2 ),
    inference(superposition,[],[f95,f64])).

fof(f95,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK1,sK1,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f393,plain,
    ( spl5_28
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f388,f284,f390])).

fof(f388,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))
    | ~ spl5_16 ),
    inference(resolution,[],[f286,f86])).

fof(f286,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f284])).

fof(f354,plain,
    ( spl5_18
    | spl5_1 ),
    inference(avatar_split_clause,[],[f353,f88,f294])).

fof(f353,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(equality_resolution,[],[f180])).

fof(f180,plain,
    ( ! [X2] :
        ( k1_enumset1(sK0,sK0,sK1) != X2
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),k1_enumset1(sK0,sK0,sK1))
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),X2) )
    | spl5_1 ),
    inference(superposition,[],[f90,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f344,plain,
    ( spl5_16
    | spl5_25
    | spl5_2 ),
    inference(avatar_split_clause,[],[f339,f93,f341,f284])).

fof(f339,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,
    ( ! [X1] :
        ( k1_enumset1(sK1,sK1,sK1) != X1
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),k1_enumset1(sK0,sK0,sK1))
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),X1) )
    | spl5_2 ),
    inference(superposition,[],[f95,f66])).

fof(f338,plain,
    ( spl5_14
    | spl5_24
    | spl5_3 ),
    inference(avatar_split_clause,[],[f333,f98,f335,f274])).

fof(f333,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f178])).

fof(f178,plain,
    ( ! [X0] :
        ( k1_enumset1(sK0,sK0,sK0) != X0
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),k1_enumset1(sK0,sK0,sK1))
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f100,f66])).

fof(f318,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f309,f305,f315,f311])).

fof(f305,plain,
    ( spl5_20
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f309,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_20 ),
    inference(resolution,[],[f307,f86])).

fof(f307,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f305])).

fof(f308,plain,
    ( spl5_20
    | spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f303,f221,f103,f305])).

fof(f103,plain,
    ( spl5_4
  <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f221,plain,
    ( spl5_12
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f303,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f302,f222])).

fof(f222,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f221])).

fof(f302,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f181])).

fof(f181,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),k1_enumset1(sK0,sK0,sK1))
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),X3) )
    | spl5_4 ),
    inference(superposition,[],[f105,f66])).

fof(f105,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f291,plain,
    ( spl5_16
    | ~ spl5_17
    | spl5_2 ),
    inference(avatar_split_clause,[],[f282,f93,f288,f284])).

fof(f282,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,
    ( ! [X1] :
        ( k1_enumset1(sK1,sK1,sK1) != X1
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),sK2)
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),X1) )
    | spl5_2 ),
    inference(superposition,[],[f95,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f281,plain,
    ( spl5_14
    | ~ spl5_15
    | spl5_3 ),
    inference(avatar_split_clause,[],[f272,f98,f278,f274])).

fof(f272,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f164])).

fof(f164,plain,
    ( ! [X0] :
        ( k1_enumset1(sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),sK2)
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f100,f65])).

fof(f271,plain,
    ( ~ spl5_13
    | spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f266,f221,f103,f268])).

fof(f266,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f265,f222])).

fof(f265,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),sK2)
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),X3) )
    | spl5_4 ),
    inference(superposition,[],[f105,f65])).

fof(f233,plain,(
    ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f60,f219])).

fof(f219,plain,
    ( ! [X0,X1] : ~ r1_tarski(X0,X1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl5_11
  <=> ! [X1,X0] : ~ r1_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f223,plain,
    ( spl5_11
    | spl5_12 ),
    inference(avatar_split_clause,[],[f216,f221,f218])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f135,f195])).

fof(f195,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f134,f60])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f80,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f81,f61])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f59,f103])).

fof(f59,plain,(
    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f29,f36,f35])).

fof(f29,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f101,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f58,f98])).

fof(f58,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f30,f36,f35,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f93])).

fof(f57,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f31,f36,f35,f55])).

fof(f31,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f56,f88])).

fof(f56,plain,(
    k1_enumset1(sK0,sK0,sK1) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f35,f36,f35])).

fof(f32,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (24263)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.49  % (24268)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (24281)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.50  % (24284)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (24265)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (24264)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (24270)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (24269)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (24276)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (24280)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (24271)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (24283)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (24274)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (24266)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (24275)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (24275)Refutation not found, incomplete strategy% (24275)------------------------------
% 0.20/0.52  % (24275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24273)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (24273)Refutation not found, incomplete strategy% (24273)------------------------------
% 0.20/0.52  % (24273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24273)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24273)Memory used [KB]: 10618
% 0.20/0.52  % (24273)Time elapsed: 0.124 s
% 0.20/0.52  % (24273)------------------------------
% 0.20/0.52  % (24273)------------------------------
% 0.20/0.53  % (24288)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (24275)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24275)Memory used [KB]: 1663
% 0.20/0.53  % (24275)Time elapsed: 0.085 s
% 0.20/0.53  % (24275)------------------------------
% 0.20/0.53  % (24275)------------------------------
% 0.20/0.53  % (24288)Refutation not found, incomplete strategy% (24288)------------------------------
% 0.20/0.53  % (24288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24288)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24288)Memory used [KB]: 6140
% 0.20/0.53  % (24288)Time elapsed: 0.130 s
% 0.20/0.53  % (24288)------------------------------
% 0.20/0.53  % (24288)------------------------------
% 0.20/0.53  % (24267)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (24289)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (24261)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (24262)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (24290)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (24262)Refutation not found, incomplete strategy% (24262)------------------------------
% 0.20/0.53  % (24262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24262)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24262)Memory used [KB]: 1663
% 0.20/0.53  % (24262)Time elapsed: 0.127 s
% 0.20/0.53  % (24262)------------------------------
% 0.20/0.53  % (24262)------------------------------
% 0.20/0.53  % (24290)Refutation not found, incomplete strategy% (24290)------------------------------
% 0.20/0.53  % (24290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24290)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24290)Memory used [KB]: 1663
% 0.20/0.53  % (24290)Time elapsed: 0.001 s
% 0.20/0.53  % (24290)------------------------------
% 0.20/0.53  % (24290)------------------------------
% 0.20/0.53  % (24282)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (24285)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (24287)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (24279)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (24279)Refutation not found, incomplete strategy% (24279)------------------------------
% 0.20/0.54  % (24279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24286)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (24272)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (24279)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24279)Memory used [KB]: 1663
% 0.20/0.54  % (24279)Time elapsed: 0.141 s
% 0.20/0.54  % (24279)------------------------------
% 0.20/0.54  % (24279)------------------------------
% 0.20/0.54  % (24278)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (24287)Refutation not found, incomplete strategy% (24287)------------------------------
% 0.20/0.54  % (24287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24287)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24287)Memory used [KB]: 6140
% 0.20/0.54  % (24287)Time elapsed: 0.137 s
% 0.20/0.54  % (24287)------------------------------
% 0.20/0.54  % (24287)------------------------------
% 0.20/0.54  % (24285)Refutation not found, incomplete strategy% (24285)------------------------------
% 0.20/0.54  % (24285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24285)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24285)Memory used [KB]: 10618
% 0.20/0.54  % (24285)Time elapsed: 0.140 s
% 0.20/0.54  % (24285)------------------------------
% 0.20/0.54  % (24285)------------------------------
% 0.20/0.55  % (24277)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (24277)Refutation not found, incomplete strategy% (24277)------------------------------
% 0.20/0.55  % (24277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24277)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (24277)Memory used [KB]: 10618
% 0.20/0.55  % (24277)Time elapsed: 0.152 s
% 0.20/0.55  % (24277)------------------------------
% 0.20/0.55  % (24277)------------------------------
% 0.20/0.55  % (24278)Refutation not found, incomplete strategy% (24278)------------------------------
% 0.20/0.55  % (24278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (24278)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (24278)Memory used [KB]: 1663
% 0.20/0.56  % (24278)Time elapsed: 0.151 s
% 0.20/0.56  % (24278)------------------------------
% 0.20/0.56  % (24278)------------------------------
% 2.16/0.65  % (24293)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.65  % (24264)Refutation not found, incomplete strategy% (24264)------------------------------
% 2.16/0.65  % (24264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (24292)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.66  % (24261)Refutation not found, incomplete strategy% (24261)------------------------------
% 2.16/0.66  % (24261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (24261)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.66  
% 2.16/0.66  % (24261)Memory used [KB]: 1663
% 2.16/0.66  % (24261)Time elapsed: 0.251 s
% 2.16/0.66  % (24261)------------------------------
% 2.16/0.66  % (24261)------------------------------
% 2.16/0.66  % (24295)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.66  % (24298)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.66  % (24295)Refutation not found, incomplete strategy% (24295)------------------------------
% 2.16/0.66  % (24295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (24295)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.66  
% 2.16/0.66  % (24295)Memory used [KB]: 10618
% 2.16/0.66  % (24295)Time elapsed: 0.090 s
% 2.16/0.66  % (24295)------------------------------
% 2.16/0.66  % (24295)------------------------------
% 2.16/0.66  % (24264)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.66  
% 2.16/0.66  % (24264)Memory used [KB]: 6140
% 2.16/0.66  % (24264)Time elapsed: 0.248 s
% 2.16/0.66  % (24264)------------------------------
% 2.16/0.66  % (24264)------------------------------
% 2.16/0.67  % (24296)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.16/0.67  % (24293)Refutation not found, incomplete strategy% (24293)------------------------------
% 2.16/0.67  % (24293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (24293)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.67  
% 2.16/0.67  % (24293)Memory used [KB]: 6140
% 2.16/0.67  % (24293)Time elapsed: 0.110 s
% 2.16/0.67  % (24293)------------------------------
% 2.16/0.67  % (24293)------------------------------
% 2.16/0.67  % (24294)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.16/0.68  % (24291)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.68  % (24297)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.68  % (24300)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.16/0.68  % (24300)Refutation not found, incomplete strategy% (24300)------------------------------
% 2.16/0.68  % (24300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (24300)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (24300)Memory used [KB]: 10746
% 2.16/0.68  % (24300)Time elapsed: 0.091 s
% 2.16/0.68  % (24300)------------------------------
% 2.16/0.68  % (24300)------------------------------
% 2.16/0.69  % (24299)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.16/0.69  % (24276)Refutation not found, incomplete strategy% (24276)------------------------------
% 2.16/0.69  % (24276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (24276)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (24276)Memory used [KB]: 6140
% 2.16/0.70  % (24276)Time elapsed: 0.289 s
% 2.16/0.70  % (24276)------------------------------
% 2.16/0.70  % (24276)------------------------------
% 2.88/0.74  % (24292)Refutation found. Thanks to Tanya!
% 2.88/0.74  % SZS status Theorem for theBenchmark
% 2.88/0.74  % SZS output start Proof for theBenchmark
% 2.88/0.74  fof(f787,plain,(
% 2.88/0.74    $false),
% 2.88/0.74    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f223,f233,f271,f281,f291,f308,f318,f338,f344,f354,f393,f397,f408,f486,f590,f591,f592,f595,f597,f598,f746,f751,f752,f772,f777,f778,f781,f782,f783,f785,f786])).
% 2.88/0.74  fof(f786,plain,(
% 2.88/0.74    spl5_26 | ~spl5_14),
% 2.88/0.74    inference(avatar_split_clause,[],[f346,f274,f348])).
% 2.88/0.74  fof(f348,plain,(
% 2.88/0.74    spl5_26 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.88/0.74  fof(f274,plain,(
% 2.88/0.74    spl5_14 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.88/0.74  fof(f346,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | ~spl5_14),
% 2.88/0.74    inference(duplicate_literal_removal,[],[f345])).
% 2.88/0.74  fof(f345,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | ~spl5_14),
% 2.88/0.74    inference(resolution,[],[f276,f86])).
% 2.88/0.74  fof(f86,plain,(
% 2.88/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.88/0.74    inference(equality_resolution,[],[f75])).
% 2.88/0.74  fof(f75,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 2.88/0.74    inference(definition_unfolding,[],[f46,f35])).
% 2.88/0.74  fof(f35,plain,(
% 2.88/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f8])).
% 2.88/0.74  fof(f8,axiom,(
% 2.88/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.88/0.74  fof(f46,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.88/0.74    inference(cnf_transformation,[],[f26])).
% 2.88/0.74  fof(f26,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.88/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 2.88/0.74  fof(f25,plain,(
% 2.88/0.74    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.88/0.74    introduced(choice_axiom,[])).
% 2.88/0.74  fof(f24,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.88/0.74    inference(rectify,[],[f23])).
% 2.88/0.74  fof(f23,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.88/0.74    inference(flattening,[],[f22])).
% 2.88/0.74  fof(f22,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.88/0.74    inference(nnf_transformation,[],[f6])).
% 2.88/0.74  fof(f6,axiom,(
% 2.88/0.74    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.88/0.74  fof(f276,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | ~spl5_14),
% 2.88/0.74    inference(avatar_component_clause,[],[f274])).
% 2.88/0.74  fof(f785,plain,(
% 2.88/0.74    ~spl5_9 | spl5_13 | ~spl5_22),
% 2.88/0.74    inference(avatar_split_clause,[],[f519,f315,f268,f145])).
% 2.88/0.74  fof(f145,plain,(
% 2.88/0.74    spl5_9 <=> r2_hidden(sK0,sK2)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.88/0.74  fof(f268,plain,(
% 2.88/0.74    spl5_13 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.88/0.74  fof(f315,plain,(
% 2.88/0.74    spl5_22 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.88/0.74  fof(f519,plain,(
% 2.88/0.74    ~r2_hidden(sK0,sK2) | (spl5_13 | ~spl5_22)),
% 2.88/0.74    inference(superposition,[],[f270,f317])).
% 2.88/0.74  fof(f317,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_22),
% 2.88/0.74    inference(avatar_component_clause,[],[f315])).
% 2.88/0.74  fof(f270,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_13),
% 2.88/0.74    inference(avatar_component_clause,[],[f268])).
% 2.88/0.74  fof(f783,plain,(
% 2.88/0.74    spl5_40 | ~spl5_25 | spl5_28),
% 2.88/0.74    inference(avatar_split_clause,[],[f740,f390,f341,f742])).
% 2.88/0.74  fof(f742,plain,(
% 2.88/0.74    spl5_40 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.88/0.74  fof(f341,plain,(
% 2.88/0.74    spl5_25 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.88/0.74  fof(f390,plain,(
% 2.88/0.74    spl5_28 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.88/0.74  fof(f740,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | (~spl5_25 | spl5_28)),
% 2.88/0.74    inference(subsumption_resolution,[],[f739,f391])).
% 2.88/0.74  fof(f391,plain,(
% 2.88/0.74    sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | spl5_28),
% 2.88/0.74    inference(avatar_component_clause,[],[f390])).
% 2.88/0.74  fof(f739,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | ~spl5_25),
% 2.88/0.74    inference(resolution,[],[f343,f86])).
% 2.88/0.74  fof(f343,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1)) | ~spl5_25),
% 2.88/0.74    inference(avatar_component_clause,[],[f341])).
% 2.88/0.74  fof(f782,plain,(
% 2.88/0.74    spl5_10 | ~spl5_19 | ~spl5_32),
% 2.88/0.74    inference(avatar_split_clause,[],[f546,f479,f298,f149])).
% 2.88/0.74  fof(f149,plain,(
% 2.88/0.74    spl5_10 <=> r2_hidden(sK1,sK2)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.88/0.74  fof(f298,plain,(
% 2.88/0.74    spl5_19 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.88/0.74  fof(f479,plain,(
% 2.88/0.74    spl5_32 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.88/0.74  fof(f546,plain,(
% 2.88/0.74    r2_hidden(sK1,sK2) | (~spl5_19 | ~spl5_32)),
% 2.88/0.74    inference(superposition,[],[f299,f481])).
% 2.88/0.74  fof(f481,plain,(
% 2.88/0.74    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | ~spl5_32),
% 2.88/0.74    inference(avatar_component_clause,[],[f479])).
% 2.88/0.74  fof(f299,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2) | ~spl5_19),
% 2.88/0.74    inference(avatar_component_clause,[],[f298])).
% 2.88/0.74  fof(f781,plain,(
% 2.88/0.74    ~spl5_14 | spl5_3 | spl5_15 | ~spl5_24),
% 2.88/0.74    inference(avatar_split_clause,[],[f780,f335,f278,f98,f274])).
% 2.88/0.74  fof(f98,plain,(
% 2.88/0.74    spl5_3 <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) = k1_enumset1(sK0,sK0,sK0)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.88/0.74  fof(f278,plain,(
% 2.88/0.74    spl5_15 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.88/0.74  fof(f335,plain,(
% 2.88/0.74    spl5_24 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.88/0.74  fof(f780,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (spl5_3 | spl5_15 | ~spl5_24)),
% 2.88/0.74    inference(subsumption_resolution,[],[f779,f337])).
% 2.88/0.74  fof(f337,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) | ~spl5_24),
% 2.88/0.74    inference(avatar_component_clause,[],[f335])).
% 2.88/0.74  fof(f779,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (spl5_3 | spl5_15)),
% 2.88/0.74    inference(subsumption_resolution,[],[f394,f280])).
% 2.88/0.74  fof(f280,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2) | spl5_15),
% 2.88/0.74    inference(avatar_component_clause,[],[f278])).
% 2.88/0.74  fof(f394,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_3),
% 2.88/0.74    inference(equality_resolution,[],[f202])).
% 2.88/0.74  fof(f202,plain,(
% 2.88/0.74    ( ! [X0] : (k1_enumset1(sK0,sK0,sK0) != X0 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),X0)) ) | spl5_3),
% 2.88/0.74    inference(superposition,[],[f100,f64])).
% 2.88/0.74  fof(f64,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.88/0.74    inference(definition_unfolding,[],[f45,f36])).
% 2.88/0.74  fof(f36,plain,(
% 2.88/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.88/0.74    inference(cnf_transformation,[],[f3])).
% 2.88/0.74  fof(f3,axiom,(
% 2.88/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.88/0.74  fof(f45,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f21])).
% 2.88/0.74  fof(f21,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.88/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 2.88/0.74  fof(f20,plain,(
% 2.88/0.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.88/0.74    introduced(choice_axiom,[])).
% 2.88/0.74  fof(f19,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.88/0.74    inference(rectify,[],[f18])).
% 2.88/0.74  fof(f18,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.88/0.74    inference(flattening,[],[f17])).
% 2.88/0.74  fof(f17,plain,(
% 2.88/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.88/0.74    inference(nnf_transformation,[],[f1])).
% 2.88/0.74  fof(f1,axiom,(
% 2.88/0.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.88/0.74  fof(f100,plain,(
% 2.88/0.74    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK0,sK0,sK0) | spl5_3),
% 2.88/0.74    inference(avatar_component_clause,[],[f98])).
% 2.88/0.74  fof(f778,plain,(
% 2.88/0.74    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f777,plain,(
% 2.88/0.74    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | r2_hidden(sK0,sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2)),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f772,plain,(
% 2.88/0.74    spl5_16 | ~spl5_28),
% 2.88/0.74    inference(avatar_contradiction_clause,[],[f771])).
% 2.88/0.74  fof(f771,plain,(
% 2.88/0.74    $false | (spl5_16 | ~spl5_28)),
% 2.88/0.74    inference(subsumption_resolution,[],[f756,f83])).
% 2.88/0.74  fof(f83,plain,(
% 2.88/0.74    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 2.88/0.74    inference(equality_resolution,[],[f82])).
% 2.88/0.74  fof(f82,plain,(
% 2.88/0.74    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 2.88/0.74    inference(equality_resolution,[],[f73])).
% 2.88/0.74  fof(f73,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 2.88/0.74    inference(definition_unfolding,[],[f48,f35])).
% 2.88/0.74  fof(f48,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.88/0.74    inference(cnf_transformation,[],[f26])).
% 2.88/0.74  fof(f756,plain,(
% 2.88/0.74    ~r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1)) | (spl5_16 | ~spl5_28)),
% 2.88/0.74    inference(superposition,[],[f285,f392])).
% 2.88/0.74  fof(f392,plain,(
% 2.88/0.74    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | ~spl5_28),
% 2.88/0.74    inference(avatar_component_clause,[],[f390])).
% 2.88/0.74  fof(f285,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) | spl5_16),
% 2.88/0.74    inference(avatar_component_clause,[],[f284])).
% 2.88/0.74  fof(f284,plain,(
% 2.88/0.74    spl5_16 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.88/0.74  fof(f752,plain,(
% 2.88/0.74    sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f751,plain,(
% 2.88/0.74    sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | r2_hidden(sK1,sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2)),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f746,plain,(
% 2.88/0.74    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2) | ~r2_hidden(sK0,sK2)),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f598,plain,(
% 2.88/0.74    ~spl5_10 | spl5_13 | ~spl5_21),
% 2.88/0.74    inference(avatar_split_clause,[],[f321,f311,f268,f149])).
% 2.88/0.74  fof(f311,plain,(
% 2.88/0.74    spl5_21 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.88/0.74  fof(f321,plain,(
% 2.88/0.74    ~r2_hidden(sK1,sK2) | (spl5_13 | ~spl5_21)),
% 2.88/0.74    inference(superposition,[],[f270,f313])).
% 2.88/0.74  fof(f313,plain,(
% 2.88/0.74    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_21),
% 2.88/0.74    inference(avatar_component_clause,[],[f311])).
% 2.88/0.74  fof(f597,plain,(
% 2.88/0.74    spl5_36 | ~spl5_24 | spl5_26),
% 2.88/0.74    inference(avatar_split_clause,[],[f561,f348,f335,f563])).
% 2.88/0.74  fof(f563,plain,(
% 2.88/0.74    spl5_36 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.88/0.74  fof(f561,plain,(
% 2.88/0.74    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | (~spl5_24 | spl5_26)),
% 2.88/0.74    inference(subsumption_resolution,[],[f560,f349])).
% 2.88/0.74  fof(f349,plain,(
% 2.88/0.74    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | spl5_26),
% 2.88/0.74    inference(avatar_component_clause,[],[f348])).
% 2.88/0.74  fof(f560,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | ~spl5_24),
% 2.88/0.74    inference(resolution,[],[f337,f86])).
% 2.88/0.74  fof(f595,plain,(
% 2.88/0.74    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2)),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f592,plain,(
% 2.88/0.74    sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | sK0 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | r2_hidden(sK0,sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2)),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f591,plain,(
% 2.88/0.74    sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | sK1 != sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2) | ~r2_hidden(sK1,sK2)),
% 2.88/0.74    introduced(theory_tautology_sat_conflict,[])).
% 2.88/0.74  fof(f590,plain,(
% 2.88/0.74    spl5_14 | ~spl5_26),
% 2.88/0.74    inference(avatar_contradiction_clause,[],[f589])).
% 2.88/0.74  fof(f589,plain,(
% 2.88/0.74    $false | (spl5_14 | ~spl5_26)),
% 2.88/0.74    inference(subsumption_resolution,[],[f578,f83])).
% 2.88/0.74  fof(f578,plain,(
% 2.88/0.74    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | (spl5_14 | ~spl5_26)),
% 2.88/0.74    inference(superposition,[],[f275,f350])).
% 2.88/0.74  fof(f350,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)) | ~spl5_26),
% 2.88/0.74    inference(avatar_component_clause,[],[f348])).
% 2.88/0.74  fof(f275,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_14),
% 2.88/0.74    inference(avatar_component_clause,[],[f274])).
% 2.88/0.74  fof(f486,plain,(
% 2.88/0.74    spl5_32 | spl5_33 | ~spl5_18),
% 2.88/0.74    inference(avatar_split_clause,[],[f477,f294,f483,f479])).
% 2.88/0.74  fof(f483,plain,(
% 2.88/0.74    spl5_33 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.88/0.74  fof(f294,plain,(
% 2.88/0.74    spl5_18 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.88/0.74  fof(f477,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)) | ~spl5_18),
% 2.88/0.74    inference(resolution,[],[f296,f86])).
% 2.88/0.74  fof(f296,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | ~spl5_18),
% 2.88/0.74    inference(avatar_component_clause,[],[f294])).
% 2.88/0.74  fof(f408,plain,(
% 2.88/0.74    ~spl5_18 | spl5_19 | spl5_1),
% 2.88/0.74    inference(avatar_split_clause,[],[f405,f88,f298,f294])).
% 2.88/0.74  fof(f88,plain,(
% 2.88/0.74    spl5_1 <=> k1_enumset1(sK0,sK0,sK1) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.88/0.74  fof(f405,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 2.88/0.74    inference(duplicate_literal_removal,[],[f404])).
% 2.88/0.74  fof(f404,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 2.88/0.74    inference(equality_resolution,[],[f204])).
% 2.88/0.74  fof(f204,plain,(
% 2.88/0.74    ( ! [X2] : (k1_enumset1(sK0,sK0,sK1) != X2 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),X2)) ) | spl5_1),
% 2.88/0.74    inference(superposition,[],[f90,f64])).
% 2.88/0.74  fof(f90,plain,(
% 2.88/0.74    k1_enumset1(sK0,sK0,sK1) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) | spl5_1),
% 2.88/0.74    inference(avatar_component_clause,[],[f88])).
% 2.88/0.74  fof(f397,plain,(
% 2.88/0.74    ~spl5_16 | ~spl5_25 | spl5_2 | spl5_17),
% 2.88/0.74    inference(avatar_split_clause,[],[f396,f288,f93,f341,f284])).
% 2.88/0.74  fof(f93,plain,(
% 2.88/0.74    spl5_2 <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.88/0.74  fof(f288,plain,(
% 2.88/0.74    spl5_17 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.88/0.74  fof(f396,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) | (spl5_2 | spl5_17)),
% 2.88/0.74    inference(subsumption_resolution,[],[f395,f290])).
% 2.88/0.74  fof(f290,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2) | spl5_17),
% 2.88/0.74    inference(avatar_component_clause,[],[f288])).
% 2.88/0.74  fof(f395,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) | spl5_2),
% 2.88/0.74    inference(equality_resolution,[],[f203])).
% 2.88/0.74  fof(f203,plain,(
% 2.88/0.74    ( ! [X1] : (k1_enumset1(sK1,sK1,sK1) != X1 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),sK2) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),X1)) ) | spl5_2),
% 2.88/0.74    inference(superposition,[],[f95,f64])).
% 2.88/0.74  fof(f95,plain,(
% 2.88/0.74    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK1,sK1,sK1) | spl5_2),
% 2.88/0.74    inference(avatar_component_clause,[],[f93])).
% 2.88/0.74  fof(f393,plain,(
% 2.88/0.74    spl5_28 | ~spl5_16),
% 2.88/0.74    inference(avatar_split_clause,[],[f388,f284,f390])).
% 2.88/0.74  fof(f388,plain,(
% 2.88/0.74    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | ~spl5_16),
% 2.88/0.74    inference(duplicate_literal_removal,[],[f387])).
% 2.88/0.74  fof(f387,plain,(
% 2.88/0.74    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)) | ~spl5_16),
% 2.88/0.74    inference(resolution,[],[f286,f86])).
% 2.88/0.74  fof(f286,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) | ~spl5_16),
% 2.88/0.74    inference(avatar_component_clause,[],[f284])).
% 2.88/0.74  fof(f354,plain,(
% 2.88/0.74    spl5_18 | spl5_1),
% 2.88/0.74    inference(avatar_split_clause,[],[f353,f88,f294])).
% 2.88/0.74  fof(f353,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 2.88/0.74    inference(duplicate_literal_removal,[],[f352])).
% 2.88/0.74  fof(f352,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK1)),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 2.88/0.74    inference(equality_resolution,[],[f180])).
% 2.88/0.74  fof(f180,plain,(
% 2.88/0.74    ( ! [X2] : (k1_enumset1(sK0,sK0,sK1) != X2 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X2),X2)) ) | spl5_1),
% 2.88/0.74    inference(superposition,[],[f90,f66])).
% 2.88/0.74  fof(f66,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.88/0.74    inference(definition_unfolding,[],[f43,f36])).
% 2.88/0.74  fof(f43,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f21])).
% 2.88/0.74  fof(f344,plain,(
% 2.88/0.74    spl5_16 | spl5_25 | spl5_2),
% 2.88/0.74    inference(avatar_split_clause,[],[f339,f93,f341,f284])).
% 2.88/0.74  fof(f339,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) | spl5_2),
% 2.88/0.74    inference(equality_resolution,[],[f179])).
% 2.88/0.74  fof(f179,plain,(
% 2.88/0.74    ( ! [X1] : (k1_enumset1(sK1,sK1,sK1) != X1 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),X1)) ) | spl5_2),
% 2.88/0.74    inference(superposition,[],[f95,f66])).
% 2.88/0.74  fof(f338,plain,(
% 2.88/0.74    spl5_14 | spl5_24 | spl5_3),
% 2.88/0.74    inference(avatar_split_clause,[],[f333,f98,f335,f274])).
% 2.88/0.74  fof(f333,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_3),
% 2.88/0.74    inference(equality_resolution,[],[f178])).
% 2.88/0.74  fof(f178,plain,(
% 2.88/0.74    ( ! [X0] : (k1_enumset1(sK0,sK0,sK0) != X0 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),X0)) ) | spl5_3),
% 2.88/0.74    inference(superposition,[],[f100,f66])).
% 2.88/0.74  fof(f318,plain,(
% 2.88/0.74    spl5_21 | spl5_22 | ~spl5_20),
% 2.88/0.74    inference(avatar_split_clause,[],[f309,f305,f315,f311])).
% 2.88/0.74  fof(f305,plain,(
% 2.88/0.74    spl5_20 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.88/0.74  fof(f309,plain,(
% 2.88/0.74    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_20),
% 2.88/0.74    inference(resolution,[],[f307,f86])).
% 2.88/0.74  fof(f307,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | ~spl5_20),
% 2.88/0.74    inference(avatar_component_clause,[],[f305])).
% 2.88/0.74  fof(f308,plain,(
% 2.88/0.74    spl5_20 | spl5_4 | ~spl5_12),
% 2.88/0.74    inference(avatar_split_clause,[],[f303,f221,f103,f305])).
% 2.88/0.74  fof(f103,plain,(
% 2.88/0.74    spl5_4 <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.88/0.74  fof(f221,plain,(
% 2.88/0.74    spl5_12 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.88/0.74  fof(f303,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | (spl5_4 | ~spl5_12)),
% 2.88/0.74    inference(subsumption_resolution,[],[f302,f222])).
% 2.88/0.74  fof(f222,plain,(
% 2.88/0.74    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl5_12),
% 2.88/0.74    inference(avatar_component_clause,[],[f221])).
% 2.88/0.74  fof(f302,plain,(
% 2.88/0.74    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 2.88/0.74    inference(equality_resolution,[],[f181])).
% 2.88/0.74  fof(f181,plain,(
% 2.88/0.74    ( ! [X3] : (k1_xboole_0 != X3 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),k1_enumset1(sK0,sK0,sK1)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),X3)) ) | spl5_4),
% 2.88/0.74    inference(superposition,[],[f105,f66])).
% 2.88/0.74  fof(f105,plain,(
% 2.88/0.74    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) | spl5_4),
% 2.88/0.74    inference(avatar_component_clause,[],[f103])).
% 2.88/0.74  fof(f291,plain,(
% 2.88/0.74    spl5_16 | ~spl5_17 | spl5_2),
% 2.88/0.74    inference(avatar_split_clause,[],[f282,f93,f288,f284])).
% 2.88/0.74  fof(f282,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK1,sK1,sK1)) | spl5_2),
% 2.88/0.74    inference(equality_resolution,[],[f165])).
% 2.88/0.74  fof(f165,plain,(
% 2.88/0.74    ( ! [X1] : (k1_enumset1(sK1,sK1,sK1) != X1 | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X1),X1)) ) | spl5_2),
% 2.88/0.74    inference(superposition,[],[f95,f65])).
% 2.88/0.74  fof(f65,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.88/0.74    inference(definition_unfolding,[],[f44,f36])).
% 2.88/0.74  fof(f44,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f21])).
% 2.88/0.74  fof(f281,plain,(
% 2.88/0.74    spl5_14 | ~spl5_15 | spl5_3),
% 2.88/0.74    inference(avatar_split_clause,[],[f272,f98,f278,f274])).
% 2.88/0.74  fof(f272,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_3),
% 2.88/0.74    inference(equality_resolution,[],[f164])).
% 2.88/0.74  fof(f164,plain,(
% 2.88/0.74    ( ! [X0] : (k1_enumset1(sK0,sK0,sK0) != X0 | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X0),X0)) ) | spl5_3),
% 2.88/0.74    inference(superposition,[],[f100,f65])).
% 2.88/0.74  fof(f271,plain,(
% 2.88/0.74    ~spl5_13 | spl5_4 | ~spl5_12),
% 2.88/0.74    inference(avatar_split_clause,[],[f266,f221,f103,f268])).
% 2.88/0.74  fof(f266,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | (spl5_4 | ~spl5_12)),
% 2.88/0.74    inference(subsumption_resolution,[],[f265,f222])).
% 2.88/0.74  fof(f265,plain,(
% 2.88/0.74    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 2.88/0.74    inference(equality_resolution,[],[f167])).
% 2.88/0.74  fof(f167,plain,(
% 2.88/0.74    ( ! [X3] : (k1_xboole_0 != X3 | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X3),X3)) ) | spl5_4),
% 2.88/0.74    inference(superposition,[],[f105,f65])).
% 2.88/0.74  fof(f233,plain,(
% 2.88/0.74    ~spl5_11),
% 2.88/0.74    inference(avatar_contradiction_clause,[],[f229])).
% 2.88/0.74  fof(f229,plain,(
% 2.88/0.74    $false | ~spl5_11),
% 2.88/0.74    inference(subsumption_resolution,[],[f60,f219])).
% 2.88/0.74  fof(f219,plain,(
% 2.88/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1)) ) | ~spl5_11),
% 2.88/0.74    inference(avatar_component_clause,[],[f218])).
% 2.88/0.74  fof(f218,plain,(
% 2.88/0.74    spl5_11 <=> ! [X1,X0] : ~r1_tarski(X0,X1)),
% 2.88/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.88/0.74  fof(f60,plain,(
% 2.88/0.74    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.88/0.74    inference(definition_unfolding,[],[f34,f36])).
% 2.88/0.74  fof(f34,plain,(
% 2.88/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f4])).
% 2.88/0.74  fof(f4,axiom,(
% 2.88/0.74    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.88/0.74  fof(f223,plain,(
% 2.88/0.74    spl5_11 | spl5_12),
% 2.88/0.74    inference(avatar_split_clause,[],[f216,f221,f218])).
% 2.88/0.74  fof(f216,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 2.88/0.74    inference(subsumption_resolution,[],[f135,f195])).
% 2.88/0.74  fof(f195,plain,(
% 2.88/0.74    ( ! [X6,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,X6)) )),
% 2.88/0.74    inference(resolution,[],[f134,f60])).
% 2.88/0.74  fof(f134,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 2.88/0.74    inference(superposition,[],[f80,f61])).
% 2.88/0.74  fof(f61,plain,(
% 2.88/0.74    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.88/0.74    inference(definition_unfolding,[],[f38,f36])).
% 2.88/0.74  fof(f38,plain,(
% 2.88/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f16])).
% 2.88/0.74  fof(f16,plain,(
% 2.88/0.74    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.88/0.74    inference(nnf_transformation,[],[f2])).
% 2.88/0.74  fof(f2,axiom,(
% 2.88/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.88/0.74  fof(f80,plain,(
% 2.88/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.88/0.74    inference(equality_resolution,[],[f68])).
% 2.88/0.74  fof(f68,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.88/0.74    inference(definition_unfolding,[],[f41,f36])).
% 2.88/0.74  fof(f41,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.88/0.74    inference(cnf_transformation,[],[f21])).
% 2.88/0.74  fof(f135,plain,(
% 2.88/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/0.74    inference(superposition,[],[f81,f61])).
% 2.88/0.74  fof(f81,plain,(
% 2.88/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 2.88/0.74    inference(equality_resolution,[],[f69])).
% 2.88/0.74  fof(f69,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.88/0.74    inference(definition_unfolding,[],[f40,f36])).
% 2.88/0.74  fof(f40,plain,(
% 2.88/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.88/0.74    inference(cnf_transformation,[],[f21])).
% 2.88/0.74  fof(f106,plain,(
% 2.88/0.74    ~spl5_4),
% 2.88/0.74    inference(avatar_split_clause,[],[f59,f103])).
% 2.88/0.74  fof(f59,plain,(
% 2.88/0.74    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 2.88/0.74    inference(definition_unfolding,[],[f29,f36,f35])).
% 2.88/0.74  fof(f29,plain,(
% 2.88/0.74    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.88/0.74    inference(cnf_transformation,[],[f15])).
% 2.88/0.74  fof(f15,plain,(
% 2.88/0.74    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.88/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 2.88/0.74  fof(f14,plain,(
% 2.88/0.74    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.88/0.74    introduced(choice_axiom,[])).
% 2.88/0.74  fof(f12,plain,(
% 2.88/0.74    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.88/0.74    inference(ennf_transformation,[],[f11])).
% 2.88/0.74  fof(f11,negated_conjecture,(
% 2.88/0.74    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.88/0.74    inference(negated_conjecture,[],[f10])).
% 2.88/0.74  fof(f10,conjecture,(
% 2.88/0.74    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 2.88/0.74  fof(f101,plain,(
% 2.88/0.74    ~spl5_3),
% 2.88/0.74    inference(avatar_split_clause,[],[f58,f98])).
% 2.88/0.74  fof(f58,plain,(
% 2.88/0.74    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK0,sK0,sK0)),
% 2.88/0.74    inference(definition_unfolding,[],[f30,f36,f35,f55])).
% 2.88/0.74  fof(f55,plain,(
% 2.88/0.74    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.88/0.74    inference(definition_unfolding,[],[f33,f35])).
% 2.88/0.74  fof(f33,plain,(
% 2.88/0.74    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.88/0.74    inference(cnf_transformation,[],[f7])).
% 2.88/0.74  fof(f7,axiom,(
% 2.88/0.74    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.88/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.88/0.74  fof(f30,plain,(
% 2.88/0.74    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 2.88/0.74    inference(cnf_transformation,[],[f15])).
% 2.88/0.74  fof(f96,plain,(
% 2.88/0.74    ~spl5_2),
% 2.88/0.74    inference(avatar_split_clause,[],[f57,f93])).
% 2.88/0.74  fof(f57,plain,(
% 2.88/0.74    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK1,sK1,sK1)),
% 2.88/0.74    inference(definition_unfolding,[],[f31,f36,f35,f55])).
% 2.88/0.74  fof(f31,plain,(
% 2.88/0.74    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 2.88/0.74    inference(cnf_transformation,[],[f15])).
% 2.88/0.74  fof(f91,plain,(
% 2.88/0.74    ~spl5_1),
% 2.88/0.74    inference(avatar_split_clause,[],[f56,f88])).
% 2.88/0.74  fof(f56,plain,(
% 2.88/0.74    k1_enumset1(sK0,sK0,sK1) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 2.88/0.74    inference(definition_unfolding,[],[f32,f35,f36,f35])).
% 2.88/0.74  fof(f32,plain,(
% 2.88/0.74    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.88/0.74    inference(cnf_transformation,[],[f15])).
% 2.88/0.74  % SZS output end Proof for theBenchmark
% 2.88/0.74  % (24292)------------------------------
% 2.88/0.74  % (24292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.74  % (24292)Termination reason: Refutation
% 2.88/0.74  
% 2.88/0.74  % (24292)Memory used [KB]: 11257
% 2.88/0.74  % (24292)Time elapsed: 0.165 s
% 2.88/0.74  % (24292)------------------------------
% 2.88/0.74  % (24292)------------------------------
% 2.88/0.76  % (24260)Success in time 0.4 s
%------------------------------------------------------------------------------
