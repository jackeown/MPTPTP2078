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
% DateTime   : Thu Dec  3 12:40:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 551 expanded)
%              Number of equality atoms :  111 ( 172 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f78,f83,f120,f124,f140,f151,f159,f164])).

fof(f164,plain,
    ( ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f68,f115,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f115,plain,
    ( r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f68,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f159,plain,
    ( ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f68,f130,f63])).

fof(f130,plain,
    ( r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f151,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f131,f139,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f40,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f139,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_8
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f140,plain,
    ( ~ spl5_8
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f127,f80,f75,f137])).

fof(f75,plain,
    ( spl5_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f80,plain,
    ( spl5_4
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f127,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | ~ spl5_3
    | spl5_4 ),
    inference(superposition,[],[f82,f77])).

fof(f77,plain,
    ( sK0 = sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f82,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f124,plain,
    ( spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl5_2
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f73,f58,f119,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f119,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_6
  <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f58,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f73,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,
    ( spl5_5
    | ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f110,f80,f117,f113])).

fof(f110,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_4 ),
    inference(superposition,[],[f82,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f83,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f49,f80])).

fof(f49,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f28,f40,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ( sK0 = sK2
        | ~ r2_hidden(sK2,sK1) )
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f78,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f27,f75,f71])).

fof(f27,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (17987)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.47  % (17979)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.49  % (17987)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f69,f78,f83,f120,f124,f140,f151,f159,f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    $false | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f68,f115,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl5_5 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl5_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    $false | (~spl5_1 | ~spl5_7)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f68,f130,f63])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl5_7 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl5_7 | spl5_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    $false | (spl5_7 | spl5_8)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f131,f139,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f42,f40,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl5_8 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f129])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~spl5_8 | ~spl5_3 | spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f127,f80,f75,f137])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl5_3 <=> sK0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl5_4 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) | (~spl5_3 | spl5_4)),
% 0.21/0.49    inference(superposition,[],[f82,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    sK0 = sK2 | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl5_2 | spl5_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    $false | (spl5_2 | spl5_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f58,f119,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl5_6 <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.49    inference(equality_resolution,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~r2_hidden(sK2,sK1) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl5_5 | ~spl5_6 | spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f80,f117,f113])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_4),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) | ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_4),
% 0.21/0.49    inference(superposition,[],[f82,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f40])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f80])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 0.21/0.49    inference(definition_unfolding,[],[f28,f40,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~spl5_2 | spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f75,f71])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    sK0 = sK2 | ~r2_hidden(sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f66])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17987)------------------------------
% 0.21/0.49  % (17987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17987)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17987)Memory used [KB]: 10746
% 0.21/0.49  % (17987)Time elapsed: 0.080 s
% 0.21/0.49  % (17987)------------------------------
% 0.21/0.49  % (17987)------------------------------
% 0.21/0.49  % (17963)Success in time 0.135 s
%------------------------------------------------------------------------------
