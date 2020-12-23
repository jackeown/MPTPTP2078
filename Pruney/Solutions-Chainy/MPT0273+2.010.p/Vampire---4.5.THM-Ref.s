%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:19 EST 2020

% Result     : Theorem 3.83s
% Output     : Refutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 337 expanded)
%              Number of leaves         :   20 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  528 (2091 expanded)
%              Number of equality atoms :  171 ( 690 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f86,f87,f203,f673,f1152,f1212,f2075,f2125,f2256,f2268,f2279,f2307])).

fof(f2307,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f2306])).

fof(f2306,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f2305,f60])).

fof(f60,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f2305,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(superposition,[],[f2282,f79])).

fof(f79,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_4
  <=> k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2282,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f67,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f67,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2279,plain,
    ( spl6_1
    | spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f336,f175,f73,f65])).

fof(f73,plain,
    ( spl6_3
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f175,plain,
    ( spl6_8
  <=> r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f336,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2)
    | r2_hidden(sK0,sK2)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f325,f60])).

fof(f325,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2)
    | r2_hidden(sK0,sK2)
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl6_8 ),
    inference(superposition,[],[f39,f227])).

fof(f227,plain,
    ( sK0 = sK3(k1_tarski(sK0),sK2,k1_tarski(sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f177,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f177,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2268,plain,
    ( spl6_2
    | ~ spl6_41 ),
    inference(avatar_contradiction_clause,[],[f2267])).

fof(f2267,plain,
    ( $false
    | spl6_2
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f2260,f71])).

fof(f71,plain,
    ( sK0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f2260,plain,
    ( sK0 = sK1
    | ~ spl6_41 ),
    inference(resolution,[],[f2133,f61])).

fof(f2133,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f2132,plain,
    ( spl6_41
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f2256,plain,
    ( spl6_41
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f2255,f82,f78,f2132])).

fof(f82,plain,
    ( spl6_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2255,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f2231,f55])).

fof(f55,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f2231,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl6_4
    | spl6_5 ),
    inference(resolution,[],[f2156,f84])).

fof(f84,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f2156,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK2)
        | r2_hidden(X4,k1_tarski(sK0))
        | ~ r2_hidden(X4,k2_tarski(sK0,sK1)) )
    | ~ spl6_4 ),
    inference(superposition,[],[f51,f79])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2125,plain,
    ( spl6_1
    | spl6_4
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f2124])).

fof(f2124,plain,
    ( $false
    | spl6_1
    | spl6_4
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f2123,f57])).

fof(f57,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2123,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl6_1
    | spl6_4
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f2122,f66])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f2122,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl6_4
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f2121,f80])).

fof(f80,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f2121,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f2105,f60])).

fof(f2105,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl6_32 ),
    inference(superposition,[],[f39,f1207])).

fof(f1207,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1205,plain,
    ( spl6_32
  <=> sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f2075,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f2074])).

fof(f2074,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f2073,f83])).

fof(f83,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f2073,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f2072,f80])).

fof(f2072,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f2059,f406])).

fof(f406,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f384,f74])).

fof(f74,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f384,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f83,f52])).

fof(f2059,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ spl6_33 ),
    inference(superposition,[],[f38,f1211])).

fof(f1211,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f1209])).

fof(f1209,plain,
    ( spl6_33
  <=> sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1212,plain,
    ( spl6_32
    | spl6_33
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f1196,f670,f1209,f1205])).

fof(f670,plain,
    ( spl6_27
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1196,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))
    | ~ spl6_27 ),
    inference(resolution,[],[f672,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f672,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f670])).

fof(f1152,plain,
    ( ~ spl6_26
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1151])).

fof(f1151,plain,
    ( $false
    | ~ spl6_26
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1141,f1150])).

fof(f1150,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl6_26
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1140,f57])).

fof(f1140,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ r2_hidden(sK0,k2_tarski(sK0,sK1)) )
    | ~ spl6_26
    | spl6_27 ),
    inference(resolution,[],[f1133,f51])).

fof(f1133,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),X0))
    | ~ spl6_26
    | spl6_27 ),
    inference(forward_demodulation,[],[f1126,f1099])).

fof(f1099,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))
    | ~ spl6_26 ),
    inference(resolution,[],[f668,f61])).

fof(f668,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f666])).

fof(f666,plain,
    ( spl6_26
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1126,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k4_xboole_0(k2_tarski(sK0,sK1),X0))
    | spl6_27 ),
    inference(resolution,[],[f671,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f671,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f670])).

fof(f1141,plain,
    ( ! [X2,X1] : ~ r2_hidden(sK0,k4_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),X1),X2))
    | ~ spl6_26
    | spl6_27 ),
    inference(resolution,[],[f1133,f53])).

fof(f673,plain,
    ( spl6_26
    | spl6_27
    | spl6_4 ),
    inference(avatar_split_clause,[],[f648,f78,f670,f666])).

fof(f648,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1))
    | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f389])).

fof(f389,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != X0
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0) )
    | spl6_4 ),
    inference(superposition,[],[f80,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f203,plain,
    ( spl6_8
    | spl6_3 ),
    inference(avatar_split_clause,[],[f201,f73,f175])).

fof(f201,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | spl6_3 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != X0
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) )
    | spl6_3 ),
    inference(superposition,[],[f75,f37])).

fof(f75,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f87,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f30,f65,f78])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f86,plain,
    ( spl6_4
    | spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f31,f69,f82,f78])).

fof(f31,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,
    ( ~ spl6_4
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f32,f82,f65,f78])).

fof(f32,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f63,f73,f69,f65])).

fof(f63,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK2)
    | sK0 != sK1
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f62,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK2) ),
    inference(inner_rewriting,[],[f33])).

fof(f33,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:28:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (17293)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (17304)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (17296)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (17295)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (17292)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (17312)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (17299)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (17297)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (17315)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (17313)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (17294)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (17314)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (17306)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (17291)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (17300)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (17319)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (17298)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (17309)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (17307)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (17305)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (17308)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (17320)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (17311)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (17301)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (17303)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (17317)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (17307)Refutation not found, incomplete strategy% (17307)------------------------------
% 0.21/0.56  % (17307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17316)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (17305)Refutation not found, incomplete strategy% (17305)------------------------------
% 0.21/0.56  % (17305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17305)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (17305)Memory used [KB]: 1663
% 0.21/0.57  % (17305)Time elapsed: 0.150 s
% 0.21/0.57  % (17305)------------------------------
% 0.21/0.57  % (17305)------------------------------
% 0.21/0.57  % (17320)Refutation not found, incomplete strategy% (17320)------------------------------
% 0.21/0.57  % (17320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (17308)Refutation not found, incomplete strategy% (17308)------------------------------
% 1.58/0.58  % (17308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (17308)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (17308)Memory used [KB]: 1663
% 1.58/0.58  % (17308)Time elapsed: 0.159 s
% 1.58/0.58  % (17308)------------------------------
% 1.58/0.58  % (17308)------------------------------
% 1.58/0.58  % (17310)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.58/0.58  % (17320)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  % (17307)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  
% 1.58/0.58  % (17320)Memory used [KB]: 1663
% 1.58/0.58  % (17307)Memory used [KB]: 10618
% 1.58/0.58  % (17320)Time elapsed: 0.161 s
% 1.58/0.58  % (17320)------------------------------
% 1.58/0.58  % (17320)------------------------------
% 1.58/0.58  % (17307)Time elapsed: 0.138 s
% 1.58/0.58  % (17307)------------------------------
% 1.58/0.58  % (17307)------------------------------
% 1.58/0.59  % (17302)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.58/0.59  % (17318)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.78/0.61  % (17302)Refutation not found, incomplete strategy% (17302)------------------------------
% 1.78/0.61  % (17302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (17302)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (17302)Memory used [KB]: 6268
% 1.78/0.61  % (17302)Time elapsed: 0.172 s
% 1.78/0.61  % (17302)------------------------------
% 1.78/0.61  % (17302)------------------------------
% 2.54/0.74  % (17325)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.54/0.74  % (17294)Refutation not found, incomplete strategy% (17294)------------------------------
% 2.54/0.74  % (17294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.74  % (17294)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.74  
% 2.54/0.74  % (17294)Memory used [KB]: 6140
% 2.54/0.74  % (17294)Time elapsed: 0.306 s
% 2.54/0.74  % (17294)------------------------------
% 2.54/0.74  % (17294)------------------------------
% 2.54/0.75  % (17337)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.93/0.77  % (17334)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.93/0.82  % (17293)Time limit reached!
% 2.93/0.82  % (17293)------------------------------
% 2.93/0.82  % (17293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.84  % (17293)Termination reason: Time limit
% 2.93/0.84  
% 2.93/0.84  % (17293)Memory used [KB]: 6524
% 2.93/0.84  % (17293)Time elapsed: 0.404 s
% 2.93/0.84  % (17293)------------------------------
% 2.93/0.84  % (17293)------------------------------
% 2.93/0.84  % (17315)Time limit reached!
% 2.93/0.84  % (17315)------------------------------
% 2.93/0.84  % (17315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.84  % (17315)Termination reason: Time limit
% 2.93/0.84  % (17315)Termination phase: Saturation
% 2.93/0.84  
% 2.93/0.84  % (17315)Memory used [KB]: 14200
% 2.93/0.84  % (17315)Time elapsed: 0.400 s
% 2.93/0.84  % (17315)------------------------------
% 2.93/0.84  % (17315)------------------------------
% 2.93/0.85  % (17356)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.53/0.85  % (17350)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.53/0.86  % (17350)Refutation not found, incomplete strategy% (17350)------------------------------
% 3.53/0.86  % (17350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.86  % (17350)Termination reason: Refutation not found, incomplete strategy
% 3.53/0.86  
% 3.53/0.86  % (17350)Memory used [KB]: 10746
% 3.53/0.86  % (17350)Time elapsed: 0.187 s
% 3.53/0.86  % (17350)------------------------------
% 3.53/0.86  % (17350)------------------------------
% 3.53/0.86  % (17336)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.83/0.92  % (17303)Refutation found. Thanks to Tanya!
% 3.83/0.92  % SZS status Theorem for theBenchmark
% 3.83/0.92  % SZS output start Proof for theBenchmark
% 3.83/0.92  fof(f2308,plain,(
% 3.83/0.92    $false),
% 3.83/0.92    inference(avatar_sat_refutation,[],[f76,f85,f86,f87,f203,f673,f1152,f1212,f2075,f2125,f2256,f2268,f2279,f2307])).
% 3.83/0.92  fof(f2307,plain,(
% 3.83/0.92    ~spl6_1 | ~spl6_4),
% 3.83/0.92    inference(avatar_contradiction_clause,[],[f2306])).
% 3.83/0.92  fof(f2306,plain,(
% 3.83/0.92    $false | (~spl6_1 | ~spl6_4)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2305,f60])).
% 3.83/0.92  fof(f60,plain,(
% 3.83/0.92    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.83/0.92    inference(equality_resolution,[],[f59])).
% 3.83/0.92  fof(f59,plain,(
% 3.83/0.92    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.83/0.92    inference(equality_resolution,[],[f47])).
% 3.83/0.92  fof(f47,plain,(
% 3.83/0.92    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.83/0.92    inference(cnf_transformation,[],[f29])).
% 3.83/0.92  fof(f29,plain,(
% 3.83/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.83/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 3.83/0.92  fof(f28,plain,(
% 3.83/0.92    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 3.83/0.92    introduced(choice_axiom,[])).
% 3.83/0.92  fof(f27,plain,(
% 3.83/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.83/0.92    inference(rectify,[],[f26])).
% 3.83/0.92  fof(f26,plain,(
% 3.83/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.83/0.92    inference(nnf_transformation,[],[f4])).
% 3.83/0.92  fof(f4,axiom,(
% 3.83/0.92    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.83/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 3.83/0.92  fof(f2305,plain,(
% 3.83/0.92    ~r2_hidden(sK0,k1_tarski(sK0)) | (~spl6_1 | ~spl6_4)),
% 3.83/0.92    inference(superposition,[],[f2282,f79])).
% 3.83/0.92  fof(f79,plain,(
% 3.83/0.92    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl6_4),
% 3.83/0.92    inference(avatar_component_clause,[],[f78])).
% 3.83/0.92  fof(f78,plain,(
% 3.83/0.92    spl6_4 <=> k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.83/0.92  fof(f2282,plain,(
% 3.83/0.92    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK2))) ) | ~spl6_1),
% 3.83/0.92    inference(resolution,[],[f67,f52])).
% 3.83/0.92  fof(f52,plain,(
% 3.83/0.92    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.83/0.92    inference(equality_resolution,[],[f35])).
% 3.83/0.92  fof(f35,plain,(
% 3.83/0.92    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.83/0.92    inference(cnf_transformation,[],[f20])).
% 3.83/0.92  fof(f20,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.83/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 3.83/0.92  fof(f19,plain,(
% 3.83/0.92    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.83/0.92    introduced(choice_axiom,[])).
% 3.83/0.92  fof(f18,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.83/0.92    inference(rectify,[],[f17])).
% 3.83/0.92  fof(f17,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.83/0.92    inference(flattening,[],[f16])).
% 3.83/0.92  fof(f16,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.83/0.92    inference(nnf_transformation,[],[f1])).
% 3.83/0.92  fof(f1,axiom,(
% 3.83/0.92    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.83/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.83/0.92  fof(f67,plain,(
% 3.83/0.92    r2_hidden(sK0,sK2) | ~spl6_1),
% 3.83/0.92    inference(avatar_component_clause,[],[f65])).
% 3.83/0.92  fof(f65,plain,(
% 3.83/0.92    spl6_1 <=> r2_hidden(sK0,sK2)),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.83/0.92  fof(f2279,plain,(
% 3.83/0.92    spl6_1 | spl6_3 | ~spl6_8),
% 3.83/0.92    inference(avatar_split_clause,[],[f336,f175,f73,f65])).
% 3.83/0.92  fof(f73,plain,(
% 3.83/0.92    spl6_3 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2)),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.83/0.92  fof(f175,plain,(
% 3.83/0.92    spl6_8 <=> r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0))),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 3.83/0.92  fof(f336,plain,(
% 3.83/0.92    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2) | r2_hidden(sK0,sK2) | ~spl6_8),
% 3.83/0.92    inference(subsumption_resolution,[],[f325,f60])).
% 3.83/0.92  fof(f325,plain,(
% 3.83/0.92    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2) | r2_hidden(sK0,sK2) | ~spl6_8),
% 3.83/0.92    inference(duplicate_literal_removal,[],[f322])).
% 3.83/0.92  fof(f322,plain,(
% 3.83/0.92    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k1_tarski(sK0)) | ~spl6_8),
% 3.83/0.92    inference(superposition,[],[f39,f227])).
% 3.83/0.92  fof(f227,plain,(
% 3.83/0.92    sK0 = sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)) | ~spl6_8),
% 3.83/0.92    inference(resolution,[],[f177,f61])).
% 3.83/0.92  fof(f61,plain,(
% 3.83/0.92    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.83/0.92    inference(equality_resolution,[],[f46])).
% 3.83/0.92  fof(f46,plain,(
% 3.83/0.92    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.83/0.92    inference(cnf_transformation,[],[f29])).
% 3.83/0.92  fof(f177,plain,(
% 3.83/0.92    r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_8),
% 3.83/0.92    inference(avatar_component_clause,[],[f175])).
% 3.83/0.92  fof(f39,plain,(
% 3.83/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.83/0.92    inference(cnf_transformation,[],[f20])).
% 3.83/0.92  fof(f2268,plain,(
% 3.83/0.92    spl6_2 | ~spl6_41),
% 3.83/0.92    inference(avatar_contradiction_clause,[],[f2267])).
% 3.83/0.92  fof(f2267,plain,(
% 3.83/0.92    $false | (spl6_2 | ~spl6_41)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2260,f71])).
% 3.83/0.92  fof(f71,plain,(
% 3.83/0.92    sK0 != sK1 | spl6_2),
% 3.83/0.92    inference(avatar_component_clause,[],[f69])).
% 3.83/0.92  fof(f69,plain,(
% 3.83/0.92    spl6_2 <=> sK0 = sK1),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.83/0.92  fof(f2260,plain,(
% 3.83/0.92    sK0 = sK1 | ~spl6_41),
% 3.83/0.92    inference(resolution,[],[f2133,f61])).
% 3.83/0.92  fof(f2133,plain,(
% 3.83/0.92    r2_hidden(sK1,k1_tarski(sK0)) | ~spl6_41),
% 3.83/0.92    inference(avatar_component_clause,[],[f2132])).
% 3.83/0.92  fof(f2132,plain,(
% 3.83/0.92    spl6_41 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 3.83/0.92  fof(f2256,plain,(
% 3.83/0.92    spl6_41 | ~spl6_4 | spl6_5),
% 3.83/0.92    inference(avatar_split_clause,[],[f2255,f82,f78,f2132])).
% 3.83/0.92  fof(f82,plain,(
% 3.83/0.92    spl6_5 <=> r2_hidden(sK1,sK2)),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.83/0.92  fof(f2255,plain,(
% 3.83/0.92    r2_hidden(sK1,k1_tarski(sK0)) | (~spl6_4 | spl6_5)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2231,f55])).
% 3.83/0.92  fof(f55,plain,(
% 3.83/0.92    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 3.83/0.92    inference(equality_resolution,[],[f54])).
% 3.83/0.92  fof(f54,plain,(
% 3.83/0.92    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 3.83/0.92    inference(equality_resolution,[],[f42])).
% 3.83/0.92  fof(f42,plain,(
% 3.83/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.83/0.92    inference(cnf_transformation,[],[f25])).
% 3.83/0.92  fof(f25,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.83/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 3.83/0.92  fof(f24,plain,(
% 3.83/0.92    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.83/0.92    introduced(choice_axiom,[])).
% 3.83/0.92  fof(f23,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.83/0.92    inference(rectify,[],[f22])).
% 3.83/0.92  fof(f22,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.83/0.92    inference(flattening,[],[f21])).
% 3.83/0.92  fof(f21,plain,(
% 3.83/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.83/0.92    inference(nnf_transformation,[],[f5])).
% 3.83/0.92  fof(f5,axiom,(
% 3.83/0.92    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.83/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 3.83/0.92  fof(f2231,plain,(
% 3.83/0.92    r2_hidden(sK1,k1_tarski(sK0)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | (~spl6_4 | spl6_5)),
% 3.83/0.92    inference(resolution,[],[f2156,f84])).
% 3.83/0.92  fof(f84,plain,(
% 3.83/0.92    ~r2_hidden(sK1,sK2) | spl6_5),
% 3.83/0.92    inference(avatar_component_clause,[],[f82])).
% 3.83/0.92  fof(f2156,plain,(
% 3.83/0.92    ( ! [X4] : (r2_hidden(X4,sK2) | r2_hidden(X4,k1_tarski(sK0)) | ~r2_hidden(X4,k2_tarski(sK0,sK1))) ) | ~spl6_4),
% 3.83/0.92    inference(superposition,[],[f51,f79])).
% 3.83/0.92  fof(f51,plain,(
% 3.83/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.83/0.92    inference(equality_resolution,[],[f36])).
% 3.83/0.92  fof(f36,plain,(
% 3.83/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.83/0.92    inference(cnf_transformation,[],[f20])).
% 3.83/0.92  fof(f2125,plain,(
% 3.83/0.92    spl6_1 | spl6_4 | ~spl6_32),
% 3.83/0.92    inference(avatar_contradiction_clause,[],[f2124])).
% 3.83/0.92  fof(f2124,plain,(
% 3.83/0.92    $false | (spl6_1 | spl6_4 | ~spl6_32)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2123,f57])).
% 3.83/0.92  fof(f57,plain,(
% 3.83/0.92    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 3.83/0.92    inference(equality_resolution,[],[f56])).
% 3.83/0.92  fof(f56,plain,(
% 3.83/0.92    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 3.83/0.92    inference(equality_resolution,[],[f41])).
% 3.83/0.92  fof(f41,plain,(
% 3.83/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.83/0.92    inference(cnf_transformation,[],[f25])).
% 3.83/0.92  fof(f2123,plain,(
% 3.83/0.92    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (spl6_1 | spl6_4 | ~spl6_32)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2122,f66])).
% 3.83/0.92  fof(f66,plain,(
% 3.83/0.92    ~r2_hidden(sK0,sK2) | spl6_1),
% 3.83/0.92    inference(avatar_component_clause,[],[f65])).
% 3.83/0.92  fof(f2122,plain,(
% 3.83/0.92    r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (spl6_4 | ~spl6_32)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2121,f80])).
% 3.83/0.92  fof(f80,plain,(
% 3.83/0.92    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl6_4),
% 3.83/0.92    inference(avatar_component_clause,[],[f78])).
% 3.83/0.92  fof(f2121,plain,(
% 3.83/0.92    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl6_32),
% 3.83/0.92    inference(subsumption_resolution,[],[f2105,f60])).
% 3.83/0.92  fof(f2105,plain,(
% 3.83/0.92    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl6_32),
% 3.83/0.92    inference(superposition,[],[f39,f1207])).
% 3.83/0.92  fof(f1207,plain,(
% 3.83/0.92    sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) | ~spl6_32),
% 3.83/0.92    inference(avatar_component_clause,[],[f1205])).
% 3.83/0.92  fof(f1205,plain,(
% 3.83/0.92    spl6_32 <=> sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 3.83/0.92  fof(f2075,plain,(
% 3.83/0.92    ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_33),
% 3.83/0.92    inference(avatar_contradiction_clause,[],[f2074])).
% 3.83/0.92  fof(f2074,plain,(
% 3.83/0.92    $false | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_33)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2073,f83])).
% 3.83/0.92  fof(f83,plain,(
% 3.83/0.92    r2_hidden(sK1,sK2) | ~spl6_5),
% 3.83/0.92    inference(avatar_component_clause,[],[f82])).
% 3.83/0.92  fof(f2073,plain,(
% 3.83/0.92    ~r2_hidden(sK1,sK2) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_33)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2072,f80])).
% 3.83/0.92  fof(f2072,plain,(
% 3.83/0.92    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,sK2) | (~spl6_3 | ~spl6_5 | ~spl6_33)),
% 3.83/0.92    inference(subsumption_resolution,[],[f2059,f406])).
% 3.83/0.92  fof(f406,plain,(
% 3.83/0.92    ~r2_hidden(sK1,k1_tarski(sK0)) | (~spl6_3 | ~spl6_5)),
% 3.83/0.92    inference(superposition,[],[f384,f74])).
% 3.83/0.92  fof(f74,plain,(
% 3.83/0.92    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK2) | ~spl6_3),
% 3.83/0.92    inference(avatar_component_clause,[],[f73])).
% 3.83/0.92  fof(f384,plain,(
% 3.83/0.92    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK2))) ) | ~spl6_5),
% 3.83/0.92    inference(resolution,[],[f83,f52])).
% 3.83/0.92  fof(f2059,plain,(
% 3.83/0.92    r2_hidden(sK1,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,sK2) | ~spl6_33),
% 3.83/0.92    inference(superposition,[],[f38,f1211])).
% 3.83/0.92  fof(f1211,plain,(
% 3.83/0.92    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) | ~spl6_33),
% 3.83/0.92    inference(avatar_component_clause,[],[f1209])).
% 3.83/0.92  fof(f1209,plain,(
% 3.83/0.92    spl6_33 <=> sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0))),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 3.83/0.92  fof(f38,plain,(
% 3.83/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.83/0.92    inference(cnf_transformation,[],[f20])).
% 3.83/0.92  fof(f1212,plain,(
% 3.83/0.92    spl6_32 | spl6_33 | ~spl6_27),
% 3.83/0.92    inference(avatar_split_clause,[],[f1196,f670,f1209,f1205])).
% 3.83/0.92  fof(f670,plain,(
% 3.83/0.92    spl6_27 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1))),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 3.83/0.92  fof(f1196,plain,(
% 3.83/0.92    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) | ~spl6_27),
% 3.83/0.92    inference(resolution,[],[f672,f58])).
% 3.83/0.92  fof(f58,plain,(
% 3.83/0.92    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 3.83/0.92    inference(equality_resolution,[],[f40])).
% 3.83/0.92  fof(f40,plain,(
% 3.83/0.92    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.83/0.92    inference(cnf_transformation,[],[f25])).
% 3.83/0.92  fof(f672,plain,(
% 3.83/0.92    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1)) | ~spl6_27),
% 3.83/0.92    inference(avatar_component_clause,[],[f670])).
% 3.83/0.92  fof(f1152,plain,(
% 3.83/0.92    ~spl6_26 | spl6_27),
% 3.83/0.92    inference(avatar_contradiction_clause,[],[f1151])).
% 3.83/0.92  fof(f1151,plain,(
% 3.83/0.92    $false | (~spl6_26 | spl6_27)),
% 3.83/0.92    inference(subsumption_resolution,[],[f1141,f1150])).
% 3.83/0.92  fof(f1150,plain,(
% 3.83/0.92    ( ! [X0] : (r2_hidden(sK0,X0)) ) | (~spl6_26 | spl6_27)),
% 3.83/0.92    inference(subsumption_resolution,[],[f1140,f57])).
% 3.83/0.92  fof(f1140,plain,(
% 3.83/0.92    ( ! [X0] : (r2_hidden(sK0,X0) | ~r2_hidden(sK0,k2_tarski(sK0,sK1))) ) | (~spl6_26 | spl6_27)),
% 3.83/0.92    inference(resolution,[],[f1133,f51])).
% 3.83/0.92  fof(f1133,plain,(
% 3.83/0.92    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),X0))) ) | (~spl6_26 | spl6_27)),
% 3.83/0.92    inference(forward_demodulation,[],[f1126,f1099])).
% 3.83/0.92  fof(f1099,plain,(
% 3.83/0.92    sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)) | ~spl6_26),
% 3.83/0.92    inference(resolution,[],[f668,f61])).
% 3.83/0.92  fof(f668,plain,(
% 3.83/0.92    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_26),
% 3.83/0.92    inference(avatar_component_clause,[],[f666])).
% 3.83/0.92  fof(f666,plain,(
% 3.83/0.92    spl6_26 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k1_tarski(sK0))),
% 3.83/0.92    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 3.83/0.92  fof(f1126,plain,(
% 3.83/0.92    ( ! [X0] : (~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k4_xboole_0(k2_tarski(sK0,sK1),X0))) ) | spl6_27),
% 3.83/0.92    inference(resolution,[],[f671,f53])).
% 3.83/0.92  fof(f53,plain,(
% 3.83/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.83/0.92    inference(equality_resolution,[],[f34])).
% 3.83/0.92  fof(f34,plain,(
% 3.83/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.83/0.92    inference(cnf_transformation,[],[f20])).
% 3.83/0.92  fof(f671,plain,(
% 3.83/0.92    ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1)) | spl6_27),
% 3.83/0.92    inference(avatar_component_clause,[],[f670])).
% 3.83/0.92  fof(f1141,plain,(
% 3.83/0.92    ( ! [X2,X1] : (~r2_hidden(sK0,k4_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),X1),X2))) ) | (~spl6_26 | spl6_27)),
% 3.83/0.92    inference(resolution,[],[f1133,f53])).
% 3.83/0.92  fof(f673,plain,(
% 3.83/0.92    spl6_26 | spl6_27 | spl6_4),
% 3.83/0.92    inference(avatar_split_clause,[],[f648,f78,f670,f666])).
% 3.83/0.92  fof(f648,plain,(
% 3.83/0.92    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_tarski(sK0)),k1_tarski(sK0)) | spl6_4),
% 3.83/0.92    inference(equality_resolution,[],[f389])).
% 3.83/0.92  fof(f389,plain,(
% 3.83/0.92    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0)) ) | spl6_4),
% 3.83/0.92    inference(superposition,[],[f80,f37])).
% 3.83/0.92  fof(f37,plain,(
% 3.83/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.83/0.92    inference(cnf_transformation,[],[f20])).
% 3.83/0.92  fof(f203,plain,(
% 3.83/0.92    spl6_8 | spl6_3),
% 3.83/0.92    inference(avatar_split_clause,[],[f201,f73,f175])).
% 3.83/0.92  fof(f201,plain,(
% 3.83/0.92    r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0)) | spl6_3),
% 3.83/0.92    inference(duplicate_literal_removal,[],[f200])).
% 3.83/0.92  fof(f200,plain,(
% 3.83/0.92    r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,k1_tarski(sK0)),k1_tarski(sK0)) | spl6_3),
% 3.83/0.92    inference(equality_resolution,[],[f98])).
% 3.83/0.92  fof(f98,plain,(
% 3.83/0.92    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)) ) | spl6_3),
% 3.83/0.92    inference(superposition,[],[f75,f37])).
% 3.83/0.92  fof(f75,plain,(
% 3.83/0.92    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK2) | spl6_3),
% 3.83/0.92    inference(avatar_component_clause,[],[f73])).
% 3.83/0.92  fof(f87,plain,(
% 3.83/0.92    spl6_4 | ~spl6_1),
% 3.83/0.92    inference(avatar_split_clause,[],[f30,f65,f78])).
% 3.83/0.92  fof(f30,plain,(
% 3.83/0.92    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.83/0.92    inference(cnf_transformation,[],[f15])).
% 3.83/0.92  fof(f15,plain,(
% 3.83/0.92    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 3.83/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 3.83/0.92  fof(f14,plain,(
% 3.83/0.92    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 3.83/0.92    introduced(choice_axiom,[])).
% 3.83/0.92  fof(f13,plain,(
% 3.83/0.92    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.83/0.92    inference(flattening,[],[f12])).
% 3.83/0.92  fof(f12,plain,(
% 3.83/0.92    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.83/0.92    inference(nnf_transformation,[],[f11])).
% 3.83/0.92  fof(f11,plain,(
% 3.83/0.92    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.83/0.92    inference(ennf_transformation,[],[f10])).
% 3.83/0.92  fof(f10,negated_conjecture,(
% 3.83/0.92    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.83/0.92    inference(negated_conjecture,[],[f9])).
% 3.83/0.92  fof(f9,conjecture,(
% 3.83/0.92    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.83/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 3.83/0.92  fof(f86,plain,(
% 3.83/0.92    spl6_4 | spl6_5 | spl6_2),
% 3.83/0.92    inference(avatar_split_clause,[],[f31,f69,f82,f78])).
% 3.83/0.92  fof(f31,plain,(
% 3.83/0.92    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.83/0.92    inference(cnf_transformation,[],[f15])).
% 3.83/0.92  fof(f85,plain,(
% 3.83/0.92    ~spl6_4 | spl6_1 | ~spl6_5),
% 3.83/0.92    inference(avatar_split_clause,[],[f32,f82,f65,f78])).
% 3.83/0.92  fof(f32,plain,(
% 3.83/0.92    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.83/0.92    inference(cnf_transformation,[],[f15])).
% 3.83/0.92  fof(f76,plain,(
% 3.83/0.92    spl6_1 | ~spl6_2 | ~spl6_3),
% 3.83/0.92    inference(avatar_split_clause,[],[f63,f73,f69,f65])).
% 3.83/0.92  fof(f63,plain,(
% 3.83/0.92    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK2) | sK0 != sK1 | r2_hidden(sK0,sK2)),
% 3.83/0.92    inference(forward_demodulation,[],[f62,f50])).
% 3.83/0.92  fof(f50,plain,(
% 3.83/0.92    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.83/0.92    inference(cnf_transformation,[],[f6])).
% 3.83/0.92  fof(f6,axiom,(
% 3.83/0.92    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.83/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.83/0.92  fof(f62,plain,(
% 3.83/0.92    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK2)),
% 3.83/0.92    inference(inner_rewriting,[],[f33])).
% 3.83/0.92  fof(f33,plain,(
% 3.83/0.92    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.83/0.92    inference(cnf_transformation,[],[f15])).
% 3.83/0.92  % SZS output end Proof for theBenchmark
% 3.83/0.92  % (17303)------------------------------
% 3.83/0.92  % (17303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (17303)Termination reason: Refutation
% 3.83/0.92  
% 3.83/0.92  % (17303)Memory used [KB]: 11897
% 3.83/0.92  % (17303)Time elapsed: 0.493 s
% 3.83/0.92  % (17303)------------------------------
% 3.83/0.92  % (17303)------------------------------
% 3.83/0.93  % (17290)Success in time 0.553 s
%------------------------------------------------------------------------------
