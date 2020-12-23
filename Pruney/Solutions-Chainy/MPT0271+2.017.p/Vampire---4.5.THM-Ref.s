%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  323 ( 796 expanded)
%              Number of equality atoms :   74 ( 164 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f88,f230,f351,f535,f703,f716])).

fof(f716,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f710,f714])).

fof(f714,plain,
    ( ! [X1] : r2_hidden(sK0,X1)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f709,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f709,plain,
    ( ! [X1] : r2_hidden(sK0,k2_xboole_0(X1,k1_xboole_0))
    | ~ spl6_10 ),
    inference(resolution,[],[f527,f73])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f527,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl6_10
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f710,plain,
    ( ! [X2] : ~ r2_hidden(sK0,k4_xboole_0(X2,k1_xboole_0))
    | ~ spl6_10 ),
    inference(resolution,[],[f527,f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f703,plain,
    ( spl6_10
    | ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f700,f84,f80,f526])).

fof(f80,plain,
    ( spl6_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f700,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_1
    | spl6_2 ),
    inference(forward_demodulation,[],[f699,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f699,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),sK1))
    | spl6_2 ),
    inference(resolution,[],[f542,f77])).

fof(f77,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f542,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK0,X3)
        | r2_hidden(sK0,k4_xboole_0(X3,sK1)) )
    | spl6_2 ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f535,plain,
    ( spl6_10
    | spl6_1
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f508,f227,f84,f80,f526])).

fof(f227,plain,
    ( spl6_9
  <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f508,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_9 ),
    inference(superposition,[],[f54,f376])).

fof(f376,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK1,k1_xboole_0)
    | ~ spl6_9 ),
    inference(resolution,[],[f229,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f229,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f227])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f351,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f344,f349])).

fof(f349,plain,
    ( ! [X1] : r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),X1)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f343,f67])).

fof(f343,plain,
    ( ! [X1] : r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))
    | ~ spl6_7 ),
    inference(resolution,[],[f201,f73])).

fof(f201,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_7
  <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f344,plain,
    ( ! [X2] : ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))
    | ~ spl6_7 ),
    inference(resolution,[],[f201,f71])).

fof(f230,plain,
    ( spl6_7
    | spl6_9
    | spl6_1 ),
    inference(avatar_split_clause,[],[f225,f80,f227,f199])).

fof(f225,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0) )
    | spl6_1 ),
    inference(superposition,[],[f82,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f88,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f48,f84,f80])).

fof(f48,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f87,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f49,f84,f80])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13951)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (13959)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (13978)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (13977)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (13954)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (13969)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (13961)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (13953)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (13950)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (13972)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (13963)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (13952)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (13955)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (13973)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (13975)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (13974)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (13964)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (13980)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (13980)Refutation not found, incomplete strategy% (13980)------------------------------
% 0.20/0.54  % (13980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13980)Memory used [KB]: 1663
% 0.20/0.54  % (13980)Time elapsed: 0.141 s
% 0.20/0.54  % (13980)------------------------------
% 0.20/0.54  % (13980)------------------------------
% 0.20/0.54  % (13976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (13979)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (13956)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (13966)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (13979)Refutation not found, incomplete strategy% (13979)------------------------------
% 0.20/0.54  % (13979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13958)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (13971)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (13966)Refutation not found, incomplete strategy% (13966)------------------------------
% 0.20/0.54  % (13966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13962)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (13965)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (13967)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (13960)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (13957)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (13970)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (13960)Refutation not found, incomplete strategy% (13960)------------------------------
% 0.20/0.56  % (13960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13960)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (13960)Memory used [KB]: 10746
% 0.20/0.56  % (13960)Time elapsed: 0.159 s
% 0.20/0.56  % (13960)------------------------------
% 0.20/0.56  % (13960)------------------------------
% 0.20/0.56  % (13966)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (13966)Memory used [KB]: 10618
% 0.20/0.56  % (13966)Time elapsed: 0.141 s
% 0.20/0.56  % (13966)------------------------------
% 0.20/0.56  % (13966)------------------------------
% 0.20/0.56  % (13979)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (13979)Memory used [KB]: 10746
% 0.20/0.56  % (13979)Time elapsed: 0.140 s
% 0.20/0.56  % (13979)------------------------------
% 0.20/0.56  % (13979)------------------------------
% 0.20/0.58  % (13962)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 1.90/0.61  % SZS output start Proof for theBenchmark
% 1.90/0.61  fof(f717,plain,(
% 1.90/0.61    $false),
% 1.90/0.61    inference(avatar_sat_refutation,[],[f87,f88,f230,f351,f535,f703,f716])).
% 1.90/0.61  fof(f716,plain,(
% 1.90/0.61    ~spl6_10),
% 1.90/0.61    inference(avatar_contradiction_clause,[],[f715])).
% 1.90/0.61  fof(f715,plain,(
% 1.90/0.61    $false | ~spl6_10),
% 1.90/0.61    inference(subsumption_resolution,[],[f710,f714])).
% 1.90/0.61  fof(f714,plain,(
% 1.90/0.61    ( ! [X1] : (r2_hidden(sK0,X1)) ) | ~spl6_10),
% 1.90/0.61    inference(forward_demodulation,[],[f709,f67])).
% 1.90/0.61  fof(f67,plain,(
% 1.90/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.90/0.61    inference(cnf_transformation,[],[f9])).
% 1.90/0.61  fof(f9,axiom,(
% 1.90/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.90/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.90/0.61  fof(f709,plain,(
% 1.90/0.61    ( ! [X1] : (r2_hidden(sK0,k2_xboole_0(X1,k1_xboole_0))) ) | ~spl6_10),
% 1.90/0.61    inference(resolution,[],[f527,f73])).
% 1.90/0.61  fof(f73,plain,(
% 1.90/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.90/0.61    inference(equality_resolution,[],[f58])).
% 1.90/0.61  fof(f58,plain,(
% 1.90/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.90/0.61    inference(cnf_transformation,[],[f41])).
% 1.90/0.61  fof(f41,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 1.90/0.61  fof(f40,plain,(
% 1.90/0.61    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.90/0.61    introduced(choice_axiom,[])).
% 1.90/0.61  fof(f39,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(rectify,[],[f38])).
% 1.90/0.61  fof(f38,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(flattening,[],[f37])).
% 1.90/0.61  fof(f37,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(nnf_transformation,[],[f3])).
% 1.90/0.61  fof(f3,axiom,(
% 1.90/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.90/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.90/0.61  fof(f527,plain,(
% 1.90/0.61    r2_hidden(sK0,k1_xboole_0) | ~spl6_10),
% 1.90/0.61    inference(avatar_component_clause,[],[f526])).
% 1.90/0.61  fof(f526,plain,(
% 1.90/0.61    spl6_10 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.90/0.61  fof(f710,plain,(
% 1.90/0.61    ( ! [X2] : (~r2_hidden(sK0,k4_xboole_0(X2,k1_xboole_0))) ) | ~spl6_10),
% 1.90/0.61    inference(resolution,[],[f527,f71])).
% 1.90/0.61  fof(f71,plain,(
% 1.90/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.90/0.61    inference(equality_resolution,[],[f51])).
% 1.90/0.61  fof(f51,plain,(
% 1.90/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.90/0.61    inference(cnf_transformation,[],[f36])).
% 1.90/0.61  fof(f36,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 1.90/0.61  fof(f35,plain,(
% 1.90/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.90/0.61    introduced(choice_axiom,[])).
% 1.90/0.61  fof(f34,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(rectify,[],[f33])).
% 1.90/0.61  fof(f33,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(flattening,[],[f32])).
% 1.90/0.61  fof(f32,plain,(
% 1.90/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.61    inference(nnf_transformation,[],[f4])).
% 1.90/0.61  fof(f4,axiom,(
% 1.90/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.90/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.90/0.61  fof(f703,plain,(
% 1.90/0.61    spl6_10 | ~spl6_1 | spl6_2),
% 1.90/0.61    inference(avatar_split_clause,[],[f700,f84,f80,f526])).
% 1.90/0.61  fof(f80,plain,(
% 1.90/0.61    spl6_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.90/0.61  fof(f84,plain,(
% 1.90/0.61    spl6_2 <=> r2_hidden(sK0,sK1)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.90/0.61  fof(f700,plain,(
% 1.90/0.61    r2_hidden(sK0,k1_xboole_0) | (~spl6_1 | spl6_2)),
% 1.90/0.61    inference(forward_demodulation,[],[f699,f81])).
% 1.90/0.61  fof(f81,plain,(
% 1.90/0.61    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl6_1),
% 1.90/0.61    inference(avatar_component_clause,[],[f80])).
% 1.90/0.61  fof(f699,plain,(
% 1.90/0.61    r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),sK1)) | spl6_2),
% 1.90/0.61    inference(resolution,[],[f542,f77])).
% 1.90/0.61  fof(f77,plain,(
% 1.90/0.61    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.90/0.61    inference(equality_resolution,[],[f76])).
% 1.90/0.61  fof(f76,plain,(
% 1.90/0.61    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.90/0.61    inference(equality_resolution,[],[f63])).
% 1.90/0.61  fof(f63,plain,(
% 1.90/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.90/0.61    inference(cnf_transformation,[],[f45])).
% 1.90/0.61  fof(f45,plain,(
% 1.90/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.90/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 1.90/0.61  fof(f44,plain,(
% 1.90/0.61    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.90/0.61    introduced(choice_axiom,[])).
% 1.90/0.61  fof(f43,plain,(
% 1.90/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.90/0.61    inference(rectify,[],[f42])).
% 1.90/0.61  fof(f42,plain,(
% 1.90/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.90/0.61    inference(nnf_transformation,[],[f18])).
% 1.90/0.61  fof(f18,axiom,(
% 1.90/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.90/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.90/0.61  fof(f542,plain,(
% 1.90/0.61    ( ! [X3] : (~r2_hidden(sK0,X3) | r2_hidden(sK0,k4_xboole_0(X3,sK1))) ) | spl6_2),
% 1.90/0.61    inference(resolution,[],[f86,f70])).
% 1.90/0.61  fof(f70,plain,(
% 1.90/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.90/0.61    inference(equality_resolution,[],[f52])).
% 1.90/0.61  fof(f52,plain,(
% 1.90/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.90/0.61    inference(cnf_transformation,[],[f36])).
% 1.90/0.61  fof(f86,plain,(
% 1.90/0.61    ~r2_hidden(sK0,sK1) | spl6_2),
% 1.90/0.61    inference(avatar_component_clause,[],[f84])).
% 1.90/0.61  fof(f535,plain,(
% 1.90/0.61    spl6_10 | spl6_1 | ~spl6_2 | ~spl6_9),
% 1.90/0.61    inference(avatar_split_clause,[],[f508,f227,f84,f80,f526])).
% 1.90/0.61  fof(f227,plain,(
% 1.90/0.61    spl6_9 <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.90/0.61  fof(f508,plain,(
% 1.90/0.61    ~r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,k1_xboole_0) | ~spl6_9),
% 1.90/0.61    inference(superposition,[],[f54,f376])).
% 1.90/0.61  fof(f376,plain,(
% 1.90/0.61    sK0 = sK2(k1_tarski(sK0),sK1,k1_xboole_0) | ~spl6_9),
% 1.90/0.61    inference(resolution,[],[f229,f78])).
% 1.90/0.61  fof(f78,plain,(
% 1.90/0.61    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.90/0.61    inference(equality_resolution,[],[f62])).
% 1.90/0.61  fof(f62,plain,(
% 1.90/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.90/0.61    inference(cnf_transformation,[],[f45])).
% 1.90/0.61  fof(f229,plain,(
% 1.90/0.61    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | ~spl6_9),
% 1.90/0.61    inference(avatar_component_clause,[],[f227])).
% 1.90/0.61  fof(f54,plain,(
% 1.90/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f36])).
% 1.90/0.61  fof(f351,plain,(
% 1.90/0.61    ~spl6_7),
% 1.90/0.61    inference(avatar_contradiction_clause,[],[f350])).
% 1.90/0.61  fof(f350,plain,(
% 1.90/0.61    $false | ~spl6_7),
% 1.90/0.61    inference(subsumption_resolution,[],[f344,f349])).
% 1.90/0.61  fof(f349,plain,(
% 1.90/0.61    ( ! [X1] : (r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),X1)) ) | ~spl6_7),
% 1.90/0.61    inference(forward_demodulation,[],[f343,f67])).
% 1.90/0.61  fof(f343,plain,(
% 1.90/0.61    ( ! [X1] : (r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))) ) | ~spl6_7),
% 1.90/0.61    inference(resolution,[],[f201,f73])).
% 1.90/0.61  fof(f201,plain,(
% 1.90/0.61    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) | ~spl6_7),
% 1.90/0.61    inference(avatar_component_clause,[],[f199])).
% 1.90/0.61  fof(f199,plain,(
% 1.90/0.61    spl6_7 <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.90/0.61  fof(f344,plain,(
% 1.90/0.61    ( ! [X2] : (~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))) ) | ~spl6_7),
% 1.90/0.61    inference(resolution,[],[f201,f71])).
% 1.90/0.61  fof(f230,plain,(
% 1.90/0.61    spl6_7 | spl6_9 | spl6_1),
% 1.90/0.61    inference(avatar_split_clause,[],[f225,f80,f227,f199])).
% 1.90/0.61  fof(f225,plain,(
% 1.90/0.61    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.90/0.61    inference(equality_resolution,[],[f95])).
% 1.90/0.61  fof(f95,plain,(
% 1.90/0.61    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0)) ) | spl6_1),
% 1.90/0.61    inference(superposition,[],[f82,f53])).
% 1.90/0.61  fof(f53,plain,(
% 1.90/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f36])).
% 1.90/0.61  fof(f82,plain,(
% 1.90/0.61    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl6_1),
% 1.90/0.61    inference(avatar_component_clause,[],[f80])).
% 1.90/0.61  fof(f88,plain,(
% 1.90/0.61    spl6_1 | spl6_2),
% 1.90/0.61    inference(avatar_split_clause,[],[f48,f84,f80])).
% 1.90/0.61  fof(f48,plain,(
% 1.90/0.61    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.90/0.61    inference(cnf_transformation,[],[f31])).
% 1.90/0.61  fof(f31,plain,(
% 1.90/0.61    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.90/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 1.90/0.61  fof(f30,plain,(
% 1.90/0.61    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.90/0.61    introduced(choice_axiom,[])).
% 1.90/0.61  fof(f29,plain,(
% 1.90/0.61    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.90/0.61    inference(nnf_transformation,[],[f27])).
% 1.90/0.61  fof(f27,plain,(
% 1.90/0.61    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.90/0.61    inference(ennf_transformation,[],[f25])).
% 1.90/0.61  fof(f25,negated_conjecture,(
% 1.90/0.61    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.90/0.61    inference(negated_conjecture,[],[f24])).
% 1.90/0.61  fof(f24,conjecture,(
% 1.90/0.61    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.90/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.90/0.61  fof(f87,plain,(
% 1.90/0.61    ~spl6_1 | ~spl6_2),
% 1.90/0.61    inference(avatar_split_clause,[],[f49,f84,f80])).
% 1.90/0.61  fof(f49,plain,(
% 1.90/0.61    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.90/0.61    inference(cnf_transformation,[],[f31])).
% 1.90/0.61  % SZS output end Proof for theBenchmark
% 1.90/0.61  % (13962)------------------------------
% 1.90/0.61  % (13962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (13962)Termination reason: Refutation
% 1.90/0.61  
% 1.90/0.61  % (13962)Memory used [KB]: 11001
% 1.90/0.61  % (13962)Time elapsed: 0.186 s
% 1.90/0.61  % (13962)------------------------------
% 1.90/0.61  % (13962)------------------------------
% 1.90/0.61  % (13949)Success in time 0.25 s
%------------------------------------------------------------------------------
