%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:27 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 331 expanded)
%              Number of leaves         :   16 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  408 (2139 expanded)
%              Number of equality atoms :  111 ( 540 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f60,f61,f186,f326,f384,f1081,f1120,f1126,f1142,f1187,f1235])).

fof(f1235,plain,
    ( ~ spl5_3
    | spl5_10
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl5_3
    | spl5_10
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f1224,f57])).

fof(f57,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1224,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_10
    | ~ spl5_28 ),
    inference(superposition,[],[f185,f1141])).

fof(f1141,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f1139,plain,
    ( spl5_28
  <=> sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f185,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_10
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1187,plain,
    ( ~ spl5_2
    | spl5_10
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f1186])).

fof(f1186,plain,
    ( $false
    | ~ spl5_2
    | spl5_10
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f1176,f53])).

fof(f53,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1176,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_10
    | ~ spl5_27 ),
    inference(superposition,[],[f185,f1137])).

fof(f1137,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1135,plain,
    ( spl5_27
  <=> sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1142,plain,
    ( spl5_27
    | spl5_28
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1128,f201,f1139,f1135])).

fof(f201,plain,
    ( spl5_11
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1128,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_11 ),
    inference(resolution,[],[f203,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f203,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1126,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1125,f131,f48,f201])).

fof(f48,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f131,plain,
    ( spl5_4
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1125,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f493,f1105])).

fof(f1105,plain,
    ( ! [X7] : ~ r2_hidden(X7,k1_xboole_0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1098,f1097])).

fof(f1097,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | ~ r2_hidden(X6,sK2) )
    | ~ spl5_4 ),
    inference(superposition,[],[f40,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f1098,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | r2_hidden(X7,sK2) )
    | ~ spl5_4 ),
    inference(superposition,[],[f41,f132])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f493,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(equality_resolution,[],[f397])).

fof(f397,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f50,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f1120,plain,
    ( ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f1118])).

fof(f1118,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f1105,f181])).

fof(f181,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_9
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1081,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1080])).

fof(f1080,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f1079,f1037])).

fof(f1037,plain,
    ( r2_hidden(sK3(sK2,sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | r2_hidden(sK3(sK2,sK2,X1),X1) )
    | spl5_4 ),
    inference(subsumption_resolution,[],[f149,f148])).

fof(f148,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(sK3(sK2,sK2,X0),sK2)
        | r2_hidden(sK3(sK2,sK2,X0),X0) )
    | spl5_4 ),
    inference(superposition,[],[f133,f29])).

fof(f133,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f149,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | ~ r2_hidden(sK3(sK2,sK2,X1),sK2)
        | r2_hidden(sK3(sK2,sK2,X1),X1) )
    | spl5_4 ),
    inference(superposition,[],[f133,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1079,plain,
    ( ~ r2_hidden(sK3(sK2,sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(superposition,[],[f1054,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f1054,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK2,sK2,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | spl5_4 ),
    inference(resolution,[],[f1037,f40])).

fof(f384,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f382,f340])).

fof(f340,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f337,f43])).

fof(f43,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f337,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f58,f217])).

fof(f217,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK2)
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k2_tarski(sK0,sK1)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f39,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f382,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_1
    | spl5_3 ),
    inference(superposition,[],[f362,f38])).

fof(f362,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f340,f40])).

fof(f326,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f324,f299])).

fof(f299,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f292,f45])).

fof(f45,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f292,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(resolution,[],[f217,f54])).

fof(f54,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f324,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1
    | spl5_2 ),
    inference(superposition,[],[f305,f38])).

fof(f305,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl5_1
    | spl5_2 ),
    inference(resolution,[],[f299,f40])).

fof(f186,plain,
    ( spl5_9
    | ~ spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f177,f48,f183,f179])).

fof(f177,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),sK2)
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),X1) )
    | spl5_1 ),
    inference(superposition,[],[f50,f30])).

fof(f61,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f23,f52,f48])).

fof(f23,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f60,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f24,f56,f48])).

fof(f24,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f25,f56,f52,f48])).

fof(f25,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19974)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (20002)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (19992)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (20002)Refutation not found, incomplete strategy% (20002)------------------------------
% 0.20/0.50  % (20002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (20002)Memory used [KB]: 1663
% 0.20/0.50  % (20002)Time elapsed: 0.076 s
% 0.20/0.50  % (20002)------------------------------
% 0.20/0.50  % (20002)------------------------------
% 0.20/0.50  % (19987)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (19984)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (19984)Refutation not found, incomplete strategy% (19984)------------------------------
% 0.20/0.51  % (19984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19984)Memory used [KB]: 1663
% 0.20/0.51  % (19984)Time elapsed: 0.076 s
% 0.20/0.51  % (19984)------------------------------
% 0.20/0.51  % (19984)------------------------------
% 0.20/0.51  % (19987)Refutation not found, incomplete strategy% (19987)------------------------------
% 0.20/0.51  % (19987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19975)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (19978)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (19973)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (19976)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (19972)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (19987)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19987)Memory used [KB]: 1663
% 0.20/0.51  % (19987)Time elapsed: 0.072 s
% 0.20/0.51  % (19987)------------------------------
% 0.20/0.51  % (19987)------------------------------
% 0.20/0.52  % (19971)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (20000)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (19977)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (19969)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (19994)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (19996)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (19982)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (19970)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (19985)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (19999)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (19997)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (19995)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (19991)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (19989)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (20001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (19986)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (19986)Refutation not found, incomplete strategy% (19986)------------------------------
% 0.20/0.55  % (19986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19988)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (19981)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (19980)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (19981)Refutation not found, incomplete strategy% (19981)------------------------------
% 0.20/0.55  % (19981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19986)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19986)Memory used [KB]: 10618
% 0.20/0.55  % (19986)Time elapsed: 0.140 s
% 0.20/0.55  % (19986)------------------------------
% 0.20/0.55  % (19986)------------------------------
% 0.20/0.55  % (19983)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (20001)Refutation not found, incomplete strategy% (20001)------------------------------
% 0.20/0.55  % (20001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20001)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20001)Memory used [KB]: 10874
% 0.20/0.55  % (20001)Time elapsed: 0.144 s
% 0.20/0.55  % (20001)------------------------------
% 0.20/0.55  % (20001)------------------------------
% 0.20/0.55  % (19981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19981)Memory used [KB]: 6140
% 0.20/0.55  % (19981)Time elapsed: 0.151 s
% 0.20/0.55  % (19981)------------------------------
% 0.20/0.55  % (19981)------------------------------
% 0.20/0.55  % (19980)Refutation not found, incomplete strategy% (19980)------------------------------
% 0.20/0.55  % (19980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (19980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (19980)Memory used [KB]: 10746
% 0.20/0.56  % (19980)Time elapsed: 0.151 s
% 0.20/0.56  % (19980)------------------------------
% 0.20/0.56  % (19980)------------------------------
% 0.20/0.59  % (20043)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.93/0.61  % (20045)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.05/0.63  % (19982)Refutation found. Thanks to Tanya!
% 2.05/0.63  % SZS status Theorem for theBenchmark
% 2.05/0.63  % SZS output start Proof for theBenchmark
% 2.05/0.63  fof(f1244,plain,(
% 2.05/0.63    $false),
% 2.05/0.63    inference(avatar_sat_refutation,[],[f59,f60,f61,f186,f326,f384,f1081,f1120,f1126,f1142,f1187,f1235])).
% 2.05/0.63  fof(f1235,plain,(
% 2.05/0.63    ~spl5_3 | spl5_10 | ~spl5_28),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1234])).
% 2.05/0.63  fof(f1234,plain,(
% 2.05/0.63    $false | (~spl5_3 | spl5_10 | ~spl5_28)),
% 2.05/0.63    inference(subsumption_resolution,[],[f1224,f57])).
% 2.05/0.63  fof(f57,plain,(
% 2.05/0.63    r2_hidden(sK1,sK2) | ~spl5_3),
% 2.05/0.63    inference(avatar_component_clause,[],[f56])).
% 2.05/0.63  fof(f56,plain,(
% 2.05/0.63    spl5_3 <=> r2_hidden(sK1,sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.05/0.63  fof(f1224,plain,(
% 2.05/0.63    ~r2_hidden(sK1,sK2) | (spl5_10 | ~spl5_28)),
% 2.05/0.63    inference(superposition,[],[f185,f1141])).
% 2.05/0.63  fof(f1141,plain,(
% 2.05/0.63    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl5_28),
% 2.05/0.63    inference(avatar_component_clause,[],[f1139])).
% 2.05/0.63  fof(f1139,plain,(
% 2.05/0.63    spl5_28 <=> sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.05/0.63  fof(f185,plain,(
% 2.05/0.63    ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_10),
% 2.05/0.63    inference(avatar_component_clause,[],[f183])).
% 2.05/0.63  fof(f183,plain,(
% 2.05/0.63    spl5_10 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.05/0.63  fof(f1187,plain,(
% 2.05/0.63    ~spl5_2 | spl5_10 | ~spl5_27),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1186])).
% 2.05/0.63  fof(f1186,plain,(
% 2.05/0.63    $false | (~spl5_2 | spl5_10 | ~spl5_27)),
% 2.05/0.63    inference(subsumption_resolution,[],[f1176,f53])).
% 2.05/0.63  fof(f53,plain,(
% 2.05/0.63    r2_hidden(sK0,sK2) | ~spl5_2),
% 2.05/0.63    inference(avatar_component_clause,[],[f52])).
% 2.05/0.63  fof(f52,plain,(
% 2.05/0.63    spl5_2 <=> r2_hidden(sK0,sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.05/0.63  fof(f1176,plain,(
% 2.05/0.63    ~r2_hidden(sK0,sK2) | (spl5_10 | ~spl5_27)),
% 2.05/0.63    inference(superposition,[],[f185,f1137])).
% 2.05/0.63  fof(f1137,plain,(
% 2.05/0.63    sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl5_27),
% 2.05/0.63    inference(avatar_component_clause,[],[f1135])).
% 2.05/0.63  fof(f1135,plain,(
% 2.05/0.63    spl5_27 <=> sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.05/0.63  fof(f1142,plain,(
% 2.05/0.63    spl5_27 | spl5_28 | ~spl5_11),
% 2.05/0.63    inference(avatar_split_clause,[],[f1128,f201,f1139,f1135])).
% 2.05/0.63  fof(f201,plain,(
% 2.05/0.63    spl5_11 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.05/0.63  fof(f1128,plain,(
% 2.05/0.63    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl5_11),
% 2.05/0.63    inference(resolution,[],[f203,f46])).
% 2.05/0.63  fof(f46,plain,(
% 2.05/0.63    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 2.05/0.63    inference(equality_resolution,[],[f32])).
% 2.05/0.63  fof(f32,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f22])).
% 2.05/0.63  fof(f22,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 2.05/0.63  fof(f21,plain,(
% 2.05/0.63    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f20,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.63    inference(rectify,[],[f19])).
% 2.05/0.63  fof(f19,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.63    inference(flattening,[],[f18])).
% 2.05/0.63  fof(f18,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.05/0.63    inference(nnf_transformation,[],[f4])).
% 2.05/0.63  fof(f4,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.05/0.63  fof(f203,plain,(
% 2.05/0.63    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | ~spl5_11),
% 2.05/0.63    inference(avatar_component_clause,[],[f201])).
% 2.05/0.63  fof(f1126,plain,(
% 2.05/0.63    spl5_11 | spl5_1 | ~spl5_4),
% 2.05/0.63    inference(avatar_split_clause,[],[f1125,f131,f48,f201])).
% 2.05/0.63  fof(f48,plain,(
% 2.05/0.63    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.05/0.63  fof(f131,plain,(
% 2.05/0.63    spl5_4 <=> k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.05/0.63  fof(f1125,plain,(
% 2.05/0.63    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | (spl5_1 | ~spl5_4)),
% 2.05/0.63    inference(subsumption_resolution,[],[f493,f1105])).
% 2.05/0.63  fof(f1105,plain,(
% 2.05/0.63    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) ) | ~spl5_4),
% 2.05/0.63    inference(subsumption_resolution,[],[f1098,f1097])).
% 2.05/0.63  fof(f1097,plain,(
% 2.05/0.63    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,sK2)) ) | ~spl5_4),
% 2.05/0.63    inference(superposition,[],[f40,f132])).
% 2.05/0.63  fof(f132,plain,(
% 2.05/0.63    k1_xboole_0 = k4_xboole_0(sK2,sK2) | ~spl5_4),
% 2.05/0.63    inference(avatar_component_clause,[],[f131])).
% 2.05/0.63  fof(f40,plain,(
% 2.05/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(equality_resolution,[],[f27])).
% 2.05/0.63  fof(f27,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f17,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 2.05/0.63  fof(f16,plain,(
% 2.05/0.63    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f15,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.63    inference(rectify,[],[f14])).
% 2.05/0.63  fof(f14,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.63    inference(flattening,[],[f13])).
% 2.05/0.63  fof(f13,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.63    inference(nnf_transformation,[],[f1])).
% 2.05/0.63  fof(f1,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.05/0.63  fof(f1098,plain,(
% 2.05/0.63    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0) | r2_hidden(X7,sK2)) ) | ~spl5_4),
% 2.05/0.63    inference(superposition,[],[f41,f132])).
% 2.05/0.63  fof(f41,plain,(
% 2.05/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(equality_resolution,[],[f26])).
% 2.05/0.63  fof(f26,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f493,plain,(
% 2.05/0.63    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_1),
% 2.05/0.63    inference(equality_resolution,[],[f397])).
% 2.05/0.63  fof(f397,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0)) ) | spl5_1),
% 2.05/0.63    inference(superposition,[],[f50,f29])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl5_1),
% 2.05/0.63    inference(avatar_component_clause,[],[f48])).
% 2.05/0.63  fof(f1120,plain,(
% 2.05/0.63    ~spl5_4 | ~spl5_9),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1118])).
% 2.05/0.63  fof(f1118,plain,(
% 2.05/0.63    $false | (~spl5_4 | ~spl5_9)),
% 2.05/0.63    inference(resolution,[],[f1105,f181])).
% 2.05/0.63  fof(f181,plain,(
% 2.05/0.63    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl5_9),
% 2.05/0.63    inference(avatar_component_clause,[],[f179])).
% 2.05/0.63  fof(f179,plain,(
% 2.05/0.63    spl5_9 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.05/0.63  fof(f1081,plain,(
% 2.05/0.63    spl5_4),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1080])).
% 2.05/0.63  fof(f1080,plain,(
% 2.05/0.63    $false | spl5_4),
% 2.05/0.63    inference(subsumption_resolution,[],[f1079,f1037])).
% 2.05/0.63  fof(f1037,plain,(
% 2.05/0.63    r2_hidden(sK3(sK2,sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 2.05/0.63    inference(equality_resolution,[],[f151])).
% 2.05/0.63  fof(f151,plain,(
% 2.05/0.63    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK3(sK2,sK2,X1),X1)) ) | spl5_4),
% 2.05/0.63    inference(subsumption_resolution,[],[f149,f148])).
% 2.05/0.63  fof(f148,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK3(sK2,sK2,X0),sK2) | r2_hidden(sK3(sK2,sK2,X0),X0)) ) | spl5_4),
% 2.05/0.63    inference(superposition,[],[f133,f29])).
% 2.05/0.63  fof(f133,plain,(
% 2.05/0.63    k1_xboole_0 != k4_xboole_0(sK2,sK2) | spl5_4),
% 2.05/0.63    inference(avatar_component_clause,[],[f131])).
% 2.05/0.63  fof(f149,plain,(
% 2.05/0.63    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK3(sK2,sK2,X1),sK2) | r2_hidden(sK3(sK2,sK2,X1),X1)) ) | spl5_4),
% 2.05/0.63    inference(superposition,[],[f133,f30])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f1079,plain,(
% 2.05/0.63    ~r2_hidden(sK3(sK2,sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 2.05/0.63    inference(superposition,[],[f1054,f38])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.05/0.63  fof(f1054,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(sK3(sK2,sK2,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ) | spl5_4),
% 2.05/0.63    inference(resolution,[],[f1037,f40])).
% 2.05/0.63  fof(f384,plain,(
% 2.05/0.63    ~spl5_1 | spl5_3),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f383])).
% 2.05/0.63  fof(f383,plain,(
% 2.05/0.63    $false | (~spl5_1 | spl5_3)),
% 2.05/0.63    inference(subsumption_resolution,[],[f382,f340])).
% 2.05/0.63  fof(f340,plain,(
% 2.05/0.63    r2_hidden(sK1,k1_xboole_0) | (~spl5_1 | spl5_3)),
% 2.05/0.63    inference(subsumption_resolution,[],[f337,f43])).
% 2.05/0.63  fof(f43,plain,(
% 2.05/0.63    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.05/0.63    inference(equality_resolution,[],[f42])).
% 2.05/0.63  fof(f42,plain,(
% 2.05/0.63    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.05/0.63    inference(equality_resolution,[],[f34])).
% 2.05/0.63  fof(f34,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f22])).
% 2.05/0.63  fof(f337,plain,(
% 2.05/0.63    r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | (~spl5_1 | spl5_3)),
% 2.05/0.63    inference(resolution,[],[f58,f217])).
% 2.05/0.63  fof(f217,plain,(
% 2.05/0.63    ( ! [X3] : (r2_hidden(X3,sK2) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k2_tarski(sK0,sK1))) ) | ~spl5_1),
% 2.05/0.63    inference(superposition,[],[f39,f49])).
% 2.05/0.63  fof(f49,plain,(
% 2.05/0.63    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 2.05/0.63    inference(avatar_component_clause,[],[f48])).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.05/0.63    inference(equality_resolution,[],[f28])).
% 2.05/0.63  fof(f28,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f58,plain,(
% 2.05/0.63    ~r2_hidden(sK1,sK2) | spl5_3),
% 2.05/0.63    inference(avatar_component_clause,[],[f56])).
% 2.05/0.63  fof(f382,plain,(
% 2.05/0.63    ~r2_hidden(sK1,k1_xboole_0) | (~spl5_1 | spl5_3)),
% 2.05/0.63    inference(superposition,[],[f362,f38])).
% 2.05/0.63  fof(f362,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl5_1 | spl5_3)),
% 2.05/0.63    inference(resolution,[],[f340,f40])).
% 2.05/0.63  fof(f326,plain,(
% 2.05/0.63    ~spl5_1 | spl5_2),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f325])).
% 2.05/0.63  fof(f325,plain,(
% 2.05/0.63    $false | (~spl5_1 | spl5_2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f324,f299])).
% 2.05/0.63  fof(f299,plain,(
% 2.05/0.63    r2_hidden(sK0,k1_xboole_0) | (~spl5_1 | spl5_2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f292,f45])).
% 2.05/0.63  fof(f45,plain,(
% 2.05/0.63    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.05/0.63    inference(equality_resolution,[],[f44])).
% 2.05/0.63  fof(f44,plain,(
% 2.05/0.63    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.05/0.63    inference(equality_resolution,[],[f33])).
% 2.05/0.63  fof(f33,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f22])).
% 2.05/0.63  fof(f292,plain,(
% 2.05/0.63    r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 2.05/0.63    inference(resolution,[],[f217,f54])).
% 2.05/0.63  fof(f54,plain,(
% 2.05/0.63    ~r2_hidden(sK0,sK2) | spl5_2),
% 2.05/0.63    inference(avatar_component_clause,[],[f52])).
% 2.05/0.63  fof(f324,plain,(
% 2.05/0.63    ~r2_hidden(sK0,k1_xboole_0) | (~spl5_1 | spl5_2)),
% 2.05/0.63    inference(superposition,[],[f305,f38])).
% 2.05/0.63  fof(f305,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl5_1 | spl5_2)),
% 2.05/0.63    inference(resolution,[],[f299,f40])).
% 2.05/0.63  fof(f186,plain,(
% 2.05/0.63    spl5_9 | ~spl5_10 | spl5_1),
% 2.05/0.63    inference(avatar_split_clause,[],[f177,f48,f183,f179])).
% 2.05/0.63  fof(f177,plain,(
% 2.05/0.63    ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_1),
% 2.05/0.63    inference(equality_resolution,[],[f77])).
% 2.05/0.63  fof(f77,plain,(
% 2.05/0.63    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),X1)) ) | spl5_1),
% 2.05/0.63    inference(superposition,[],[f50,f30])).
% 2.05/0.63  fof(f61,plain,(
% 2.05/0.63    spl5_1 | spl5_2),
% 2.05/0.63    inference(avatar_split_clause,[],[f23,f52,f48])).
% 2.05/0.63  fof(f23,plain,(
% 2.05/0.63    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.05/0.63    inference(cnf_transformation,[],[f12])).
% 2.05/0.63  fof(f12,plain,(
% 2.05/0.63    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 2.05/0.63  fof(f11,plain,(
% 2.05/0.63    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f10,plain,(
% 2.05/0.63    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.05/0.63    inference(flattening,[],[f9])).
% 2.05/0.63  fof(f9,plain,(
% 2.05/0.63    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.05/0.63    inference(nnf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,plain,(
% 2.05/0.63    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.05/0.63    inference(ennf_transformation,[],[f7])).
% 2.05/0.63  fof(f7,negated_conjecture,(
% 2.05/0.63    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.05/0.63    inference(negated_conjecture,[],[f6])).
% 2.05/0.63  fof(f6,conjecture,(
% 2.05/0.63    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 2.05/0.63  fof(f60,plain,(
% 2.05/0.63    spl5_1 | spl5_3),
% 2.05/0.63    inference(avatar_split_clause,[],[f24,f56,f48])).
% 2.05/0.63  fof(f24,plain,(
% 2.05/0.63    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.05/0.63    inference(cnf_transformation,[],[f12])).
% 2.05/0.63  fof(f59,plain,(
% 2.05/0.63    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 2.05/0.63    inference(avatar_split_clause,[],[f25,f56,f52,f48])).
% 2.05/0.63  fof(f25,plain,(
% 2.05/0.63    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.05/0.63    inference(cnf_transformation,[],[f12])).
% 2.05/0.63  % SZS output end Proof for theBenchmark
% 2.05/0.63  % (19982)------------------------------
% 2.05/0.63  % (19982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (19982)Termination reason: Refutation
% 2.05/0.63  
% 2.05/0.63  % (19982)Memory used [KB]: 11129
% 2.05/0.63  % (19982)Time elapsed: 0.223 s
% 2.05/0.63  % (19982)------------------------------
% 2.05/0.63  % (19982)------------------------------
% 2.07/0.63  % (19964)Success in time 0.269 s
%------------------------------------------------------------------------------
