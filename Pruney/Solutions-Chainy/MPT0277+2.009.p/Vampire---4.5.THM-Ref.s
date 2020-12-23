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
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 6.15s
% Output     : Refutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 509 expanded)
%              Number of leaves         :   24 ( 167 expanded)
%              Depth                    :   17
%              Number of atoms          :  645 (3119 expanded)
%              Number of equality atoms :  272 (1226 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4756,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f76,f81,f91,f92,f1452,f2295,f2317,f2643,f2653,f2658,f2660,f2715,f3070,f3072,f4438,f4472,f4751])).

fof(f4751,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f4750])).

fof(f4750,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f4736])).

fof(f4736,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_3
    | ~ spl6_4 ),
    inference(superposition,[],[f71,f4583])).

fof(f4583,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(X10,sK2))
    | ~ spl6_4 ),
    inference(resolution,[],[f4499,f54])).

fof(f54,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f4499,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2,X1)
        | k1_xboole_0 = k4_xboole_0(sK0,X1) )
    | ~ spl6_4 ),
    inference(superposition,[],[f41,f74])).

fof(f74,plain,
    ( sK0 = k1_tarski(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_4
  <=> sK0 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f71,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f4472,plain,
    ( ~ spl6_29
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | spl6_49
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f2888,f2655,f2650,f69,f64,f60,f718])).

fof(f718,plain,
    ( spl6_29
  <=> sK1 = sK4(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f60,plain,
    ( spl6_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f64,plain,
    ( spl6_2
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f2650,plain,
    ( spl6_49
  <=> sK2 = sK5(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f2655,plain,
    ( spl6_50
  <=> r2_hidden(sK5(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f2888,plain,
    ( sK1 != sK4(sK1,sK2,sK0)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | spl6_49
    | ~ spl6_50 ),
    inference(trivial_inequality_removal,[],[f2882])).

fof(f2882,plain,
    ( sK1 != sK4(sK1,sK2,sK0)
    | sK0 != sK0
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | spl6_49
    | ~ spl6_50 ),
    inference(resolution,[],[f2858,f2375])).

fof(f2375,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | sK1 != sK4(sK1,sK2,X1)
        | sK0 != X1 )
    | spl6_2 ),
    inference(inner_rewriting,[],[f2373])).

fof(f2373,plain,
    ( ! [X1] :
        ( sK0 != X1
        | sK1 != sK4(sK1,sK2,X1)
        | ~ r2_hidden(sK4(sK1,sK2,X1),X1) )
    | spl6_2 ),
    inference(superposition,[],[f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) != X0
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f2858,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_49
    | ~ spl6_50 ),
    inference(superposition,[],[f2657,f2833])).

fof(f2833,plain,
    ( sK1 = sK5(sK0,sK2)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f2826,f2652])).

fof(f2652,plain,
    ( sK2 != sK5(sK0,sK2)
    | spl6_49 ),
    inference(avatar_component_clause,[],[f2650])).

fof(f2826,plain,
    ( sK2 = sK5(sK0,sK2)
    | sK1 = sK5(sK0,sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(resolution,[],[f2693,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2693,plain,
    ( r2_hidden(sK5(sK0,sK2),k2_tarski(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(resolution,[],[f2678,f2657])).

fof(f2678,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | r2_hidden(X3,k2_tarski(sK1,sK2)) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f2673,f2352])).

fof(f2352,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_xboole_0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f2345,f2344])).

fof(f2344,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,k1_xboole_0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f51,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

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
    inference(flattening,[],[f15])).

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

fof(f2345,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | r2_hidden(X6,sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f52,f61])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2673,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | r2_hidden(X3,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X3,sK0) )
    | ~ spl6_3 ),
    inference(superposition,[],[f50,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f2657,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f2655])).

fof(f4438,plain,
    ( spl6_29
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_32
    | spl6_33 ),
    inference(avatar_split_clause,[],[f4433,f741,f737,f69,f60,f718])).

fof(f737,plain,
    ( spl6_32
  <=> r2_hidden(sK4(sK1,sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f741,plain,
    ( spl6_33
  <=> sK2 = sK4(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f4433,plain,
    ( sK1 = sK4(sK1,sK2,sK0)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_32
    | spl6_33 ),
    inference(subsumption_resolution,[],[f4421,f742])).

fof(f742,plain,
    ( sK2 != sK4(sK1,sK2,sK0)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f741])).

fof(f4421,plain,
    ( sK2 = sK4(sK1,sK2,sK0)
    | sK1 = sK4(sK1,sK2,sK0)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_32 ),
    inference(resolution,[],[f3334,f57])).

fof(f3334,plain,
    ( r2_hidden(sK4(sK1,sK2,sK0),k2_tarski(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_32 ),
    inference(resolution,[],[f739,f2678])).

fof(f739,plain,
    ( r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f737])).

fof(f3072,plain,
    ( spl6_44
    | ~ spl6_1
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_43 ),
    inference(avatar_split_clause,[],[f3071,f1506,f88,f78,f69,f60,f1510])).

fof(f1510,plain,
    ( spl6_44
  <=> sK2 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f78,plain,
    ( spl6_5
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f88,plain,
    ( spl6_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1506,plain,
    ( spl6_43
  <=> sK1 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f3071,plain,
    ( sK2 = sK5(sK0,sK1)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_43 ),
    inference(subsumption_resolution,[],[f3042,f1507])).

fof(f1507,plain,
    ( sK1 != sK5(sK0,sK1)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f3042,plain,
    ( sK2 = sK5(sK0,sK1)
    | sK1 = sK5(sK0,sK1)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_5
    | spl6_7 ),
    inference(resolution,[],[f2708,f57])).

fof(f2708,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_tarski(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_3
    | spl6_5
    | spl6_7 ),
    inference(resolution,[],[f2707,f2678])).

fof(f2707,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | spl6_5
    | spl6_7 ),
    inference(subsumption_resolution,[],[f2706,f90])).

fof(f90,plain,
    ( k1_xboole_0 != sK0
    | spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f2706,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | k1_xboole_0 = sK0
    | spl6_5 ),
    inference(equality_resolution,[],[f2662])).

fof(f2662,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(X0,sK1),X0)
        | k1_xboole_0 = X0 )
    | spl6_5 ),
    inference(superposition,[],[f80,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f10,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f80,plain,
    ( sK0 != k1_tarski(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f3070,plain,
    ( spl6_32
    | spl6_33
    | spl6_2
    | spl6_29 ),
    inference(avatar_split_clause,[],[f3069,f718,f64,f741,f737])).

fof(f3069,plain,
    ( sK2 = sK4(sK1,sK2,sK0)
    | r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | spl6_2
    | spl6_29 ),
    inference(subsumption_resolution,[],[f734,f66])).

fof(f734,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK2 = sK4(sK1,sK2,sK0)
    | r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | spl6_29 ),
    inference(trivial_inequality_removal,[],[f732])).

fof(f732,plain,
    ( sK1 != sK1
    | sK0 = k2_tarski(sK1,sK2)
    | sK2 = sK4(sK1,sK2,sK0)
    | r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | spl6_29 ),
    inference(superposition,[],[f720,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) = X1
      | sK4(X0,X1,X2) = X0
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f720,plain,
    ( sK1 != sK4(sK1,sK2,sK0)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f718])).

fof(f2715,plain,
    ( ~ spl6_43
    | spl6_5
    | spl6_7 ),
    inference(avatar_split_clause,[],[f2714,f88,f78,f1506])).

fof(f2714,plain,
    ( sK1 != sK5(sK0,sK1)
    | spl6_5
    | spl6_7 ),
    inference(subsumption_resolution,[],[f2713,f90])).

fof(f2713,plain,
    ( sK1 != sK5(sK0,sK1)
    | k1_xboole_0 = sK0
    | spl6_5 ),
    inference(equality_resolution,[],[f2663])).

fof(f2663,plain,
    ( ! [X1] :
        ( sK0 != X1
        | sK1 != sK5(X1,sK1)
        | k1_xboole_0 = X1 )
    | spl6_5 ),
    inference(superposition,[],[f80,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2660,plain,
    ( ~ spl6_1
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f2659])).

fof(f2659,plain,
    ( $false
    | ~ spl6_1
    | spl6_6 ),
    inference(subsumption_resolution,[],[f86,f2481])).

fof(f2481,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)
    | ~ spl6_1 ),
    inference(resolution,[],[f2351,f2354])).

fof(f2354,plain,
    ( ! [X2,X1] : ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))
    | ~ spl6_1 ),
    inference(resolution,[],[f2352,f52])).

fof(f2351,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,sK0,X1),X1)
        | k1_xboole_0 = X1 )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f2334,f2333])).

fof(f2333,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK0,X0),sK0)
        | k1_xboole_0 = X0
        | r2_hidden(sK3(sK0,sK0,X0),X0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f61,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2334,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | ~ r2_hidden(sK3(sK0,sK0,X1),sK0)
        | r2_hidden(sK3(sK0,sK0,X1),X1) )
    | ~ spl6_1 ),
    inference(superposition,[],[f61,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_6
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2658,plain,
    ( spl6_7
    | spl6_50
    | spl6_4 ),
    inference(avatar_split_clause,[],[f657,f73,f2655,f88])).

fof(f657,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | k1_xboole_0 = sK0
    | spl6_4 ),
    inference(equality_resolution,[],[f594])).

fof(f594,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK5(X0,sK2),X0)
        | k1_xboole_0 = X0 )
    | spl6_4 ),
    inference(superposition,[],[f75,f48])).

fof(f75,plain,
    ( sK0 != k1_tarski(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f2653,plain,
    ( spl6_7
    | ~ spl6_49
    | spl6_4 ),
    inference(avatar_split_clause,[],[f662,f73,f2650,f88])).

fof(f662,plain,
    ( sK2 != sK5(sK0,sK2)
    | k1_xboole_0 = sK0
    | spl6_4 ),
    inference(equality_resolution,[],[f595])).

fof(f595,plain,
    ( ! [X1] :
        ( sK0 != X1
        | sK2 != sK5(X1,sK2)
        | k1_xboole_0 = X1 )
    | spl6_4 ),
    inference(superposition,[],[f75,f49])).

fof(f2643,plain,
    ( spl6_3
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f2642])).

fof(f2642,plain,
    ( $false
    | spl6_3
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f2627])).

fof(f2627,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f71,f2465])).

fof(f2465,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,X9))
    | ~ spl6_5 ),
    inference(resolution,[],[f2329,f56])).

fof(f56,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2329,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | k1_xboole_0 = k4_xboole_0(sK0,X4) )
    | ~ spl6_5 ),
    inference(superposition,[],[f41,f79])).

fof(f79,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f2317,plain,
    ( spl6_5
    | spl6_42
    | spl6_7
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f2316,f1510,f88,f1448,f78])).

fof(f1448,plain,
    ( spl6_42
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2316,plain,
    ( r2_hidden(sK2,sK0)
    | sK0 = k1_tarski(sK1)
    | spl6_7
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f1532,f90])).

fof(f1532,plain,
    ( r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | ~ spl6_44 ),
    inference(superposition,[],[f48,f1512])).

fof(f1512,plain,
    ( sK2 = sK5(sK0,sK1)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f2295,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f2294])).

fof(f2294,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f2293,f149])).

fof(f149,plain,
    ( r2_hidden(sK3(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | r2_hidden(sK3(sK0,sK0,X1),X1) )
    | spl6_1 ),
    inference(subsumption_resolution,[],[f94,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK0,X0),sK0)
        | k1_xboole_0 != X0
        | r2_hidden(sK3(sK0,sK0,X0),X0) )
    | spl6_1 ),
    inference(superposition,[],[f62,f37])).

fof(f62,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f94,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | ~ r2_hidden(sK3(sK0,sK0,X1),sK0)
        | r2_hidden(sK3(sK0,sK0,X1),X1) )
    | spl6_1 ),
    inference(superposition,[],[f62,f38])).

fof(f2293,plain,
    ( ~ r2_hidden(sK3(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(condensation,[],[f2292])).

fof(f2292,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK3(sK0,sK0,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X6,k1_xboole_0) )
    | spl6_1 ),
    inference(superposition,[],[f308,f41])).

fof(f308,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,sK0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | spl6_1 ),
    inference(resolution,[],[f149,f51])).

fof(f1452,plain,
    ( ~ spl6_42
    | spl6_2
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f797,f741,f64,f1448])).

fof(f797,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ r2_hidden(sK2,sK0)
    | ~ spl6_33 ),
    inference(trivial_inequality_removal,[],[f794])).

fof(f794,plain,
    ( sK2 != sK2
    | sK0 = k2_tarski(sK1,sK2)
    | ~ r2_hidden(sK2,sK0)
    | ~ spl6_33 ),
    inference(superposition,[],[f47,f743])).

fof(f743,plain,
    ( sK2 = sK4(sK1,sK2,sK0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f741])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) != X1
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,
    ( spl6_3
    | spl6_7
    | spl6_5
    | spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f28,f64,f73,f78,f88,f69])).

fof(f28,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f91,plain,
    ( ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f82,f88,f84])).

fof(f82,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f30,f78,f69])).

fof(f30,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f31,f73,f69])).

fof(f31,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f58,f64,f60])).

fof(f58,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(inner_rewriting,[],[f32])).

fof(f32,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:59:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (24503)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (24507)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (24506)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (24504)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (24502)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (24517)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (24524)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (24503)Refutation not found, incomplete strategy% (24503)------------------------------
% 0.22/0.53  % (24503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24509)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (24514)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (24505)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (24516)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (24526)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (24512)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (24518)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (24528)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (24510)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (24525)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (24530)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (24521)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (24526)Refutation not found, incomplete strategy% (24526)------------------------------
% 0.22/0.54  % (24526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24520)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (24522)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (24527)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (24503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24503)Memory used [KB]: 1663
% 0.22/0.55  % (24503)Time elapsed: 0.118 s
% 0.22/0.55  % (24503)------------------------------
% 0.22/0.55  % (24503)------------------------------
% 0.22/0.55  % (24531)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (24531)Refutation not found, incomplete strategy% (24531)------------------------------
% 0.22/0.55  % (24531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24531)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24531)Memory used [KB]: 1663
% 0.22/0.55  % (24531)Time elapsed: 0.140 s
% 0.22/0.55  % (24531)------------------------------
% 0.22/0.55  % (24531)------------------------------
% 0.22/0.55  % (24519)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (24515)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (24523)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (24518)Refutation not found, incomplete strategy% (24518)------------------------------
% 0.22/0.55  % (24518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24518)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24518)Memory used [KB]: 10746
% 0.22/0.55  % (24518)Time elapsed: 0.137 s
% 0.22/0.55  % (24518)------------------------------
% 0.22/0.55  % (24518)------------------------------
% 0.22/0.55  % (24528)Refutation not found, incomplete strategy% (24528)------------------------------
% 0.22/0.55  % (24528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24528)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24528)Memory used [KB]: 6268
% 0.22/0.55  % (24528)Time elapsed: 0.139 s
% 0.22/0.55  % (24528)------------------------------
% 0.22/0.55  % (24528)------------------------------
% 0.22/0.56  % (24511)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (24529)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (24526)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (24526)Memory used [KB]: 10618
% 0.22/0.56  % (24526)Time elapsed: 0.129 s
% 0.22/0.56  % (24526)------------------------------
% 0.22/0.56  % (24526)------------------------------
% 0.22/0.56  % (24513)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (24508)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (24529)Refutation not found, incomplete strategy% (24529)------------------------------
% 0.22/0.58  % (24529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (24529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (24529)Memory used [KB]: 6268
% 0.22/0.58  % (24529)Time elapsed: 0.149 s
% 0.22/0.58  % (24529)------------------------------
% 0.22/0.58  % (24529)------------------------------
% 2.25/0.72  % (24543)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.82/0.74  % (24552)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.82/0.77  % (24550)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.15/0.78  % (24545)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.15/0.79  % (24548)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.15/0.81  % (24557)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.69/0.84  % (24512)Refutation not found, incomplete strategy% (24512)------------------------------
% 3.69/0.84  % (24512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.84  % (24512)Termination reason: Refutation not found, incomplete strategy
% 3.69/0.84  
% 3.69/0.84  % (24512)Memory used [KB]: 12025
% 3.69/0.84  % (24512)Time elapsed: 0.420 s
% 3.69/0.84  % (24512)------------------------------
% 3.69/0.84  % (24512)------------------------------
% 3.69/0.85  % (24504)Time limit reached!
% 3.69/0.85  % (24504)------------------------------
% 3.69/0.85  % (24504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.85  % (24504)Termination reason: Time limit
% 3.69/0.85  
% 3.69/0.85  % (24504)Memory used [KB]: 6396
% 3.69/0.85  % (24504)Time elapsed: 0.429 s
% 3.69/0.85  % (24504)------------------------------
% 3.69/0.85  % (24504)------------------------------
% 4.30/0.93  % (24508)Time limit reached!
% 4.30/0.93  % (24508)------------------------------
% 4.30/0.93  % (24508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.94  % (24508)Termination reason: Time limit
% 4.30/0.94  % (24508)Termination phase: Saturation
% 4.30/0.94  
% 4.30/0.94  % (24508)Memory used [KB]: 13176
% 4.30/0.94  % (24508)Time elapsed: 0.500 s
% 4.30/0.94  % (24508)------------------------------
% 4.30/0.94  % (24508)------------------------------
% 4.51/0.98  % (24516)Time limit reached!
% 4.51/0.98  % (24516)------------------------------
% 4.51/0.98  % (24516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.98  % (24516)Termination reason: Time limit
% 4.51/0.98  % (24516)Termination phase: Saturation
% 4.51/0.98  
% 4.51/0.98  % (24516)Memory used [KB]: 2942
% 4.51/0.98  % (24516)Time elapsed: 0.509 s
% 4.51/0.98  % (24516)------------------------------
% 4.51/0.98  % (24516)------------------------------
% 4.51/1.02  % (24562)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.05/1.06  % (24563)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.30/1.08  % (24509)Time limit reached!
% 5.30/1.08  % (24509)------------------------------
% 5.30/1.08  % (24509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.30/1.08  % (24509)Termination reason: Time limit
% 5.30/1.08  % (24509)Termination phase: Saturation
% 5.30/1.08  
% 5.30/1.08  % (24509)Memory used [KB]: 4477
% 5.30/1.08  % (24509)Time elapsed: 0.600 s
% 5.30/1.08  % (24509)------------------------------
% 5.30/1.08  % (24509)------------------------------
% 5.30/1.08  % (24565)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.30/1.10  % (24530)Refutation not found, incomplete strategy% (24530)------------------------------
% 5.30/1.10  % (24530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.30/1.10  % (24530)Termination reason: Refutation not found, incomplete strategy
% 5.30/1.10  
% 5.30/1.10  % (24530)Memory used [KB]: 12792
% 5.30/1.10  % (24530)Time elapsed: 0.653 s
% 5.30/1.10  % (24530)------------------------------
% 5.30/1.10  % (24530)------------------------------
% 5.30/1.14  % (24566)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 5.30/1.14  % (24566)Refutation not found, incomplete strategy% (24566)------------------------------
% 5.30/1.14  % (24566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.15/1.15  % (24566)Termination reason: Refutation not found, incomplete strategy
% 6.15/1.15  
% 6.15/1.15  % (24566)Memory used [KB]: 10746
% 6.15/1.15  % (24566)Time elapsed: 0.149 s
% 6.15/1.15  % (24566)------------------------------
% 6.15/1.15  % (24566)------------------------------
% 6.15/1.16  % (24514)Refutation found. Thanks to Tanya!
% 6.15/1.16  % SZS status Theorem for theBenchmark
% 6.15/1.17  % (24567)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.35/1.19  % SZS output start Proof for theBenchmark
% 6.35/1.19  fof(f4756,plain,(
% 6.35/1.19    $false),
% 6.35/1.19    inference(avatar_sat_refutation,[],[f67,f76,f81,f91,f92,f1452,f2295,f2317,f2643,f2653,f2658,f2660,f2715,f3070,f3072,f4438,f4472,f4751])).
% 6.35/1.19  fof(f4751,plain,(
% 6.35/1.19    spl6_3 | ~spl6_4),
% 6.35/1.19    inference(avatar_contradiction_clause,[],[f4750])).
% 6.35/1.19  fof(f4750,plain,(
% 6.35/1.19    $false | (spl6_3 | ~spl6_4)),
% 6.35/1.19    inference(trivial_inequality_removal,[],[f4736])).
% 6.35/1.19  fof(f4736,plain,(
% 6.35/1.19    k1_xboole_0 != k1_xboole_0 | (spl6_3 | ~spl6_4)),
% 6.35/1.19    inference(superposition,[],[f71,f4583])).
% 6.35/1.19  fof(f4583,plain,(
% 6.35/1.19    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(X10,sK2))) ) | ~spl6_4),
% 6.35/1.19    inference(resolution,[],[f4499,f54])).
% 6.35/1.19  fof(f54,plain,(
% 6.35/1.19    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 6.35/1.19    inference(equality_resolution,[],[f53])).
% 6.35/1.19  fof(f53,plain,(
% 6.35/1.19    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 6.35/1.19    inference(equality_resolution,[],[f44])).
% 6.35/1.19  fof(f44,plain,(
% 6.35/1.19    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.35/1.19    inference(cnf_transformation,[],[f25])).
% 6.35/1.19  fof(f25,plain,(
% 6.35/1.19    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.35/1.19    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 6.35/1.19  fof(f24,plain,(
% 6.35/1.19    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 6.35/1.19    introduced(choice_axiom,[])).
% 6.35/1.19  fof(f23,plain,(
% 6.35/1.19    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.35/1.19    inference(rectify,[],[f22])).
% 6.35/1.19  fof(f22,plain,(
% 6.35/1.19    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.35/1.19    inference(flattening,[],[f21])).
% 6.35/1.19  fof(f21,plain,(
% 6.35/1.19    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.35/1.19    inference(nnf_transformation,[],[f2])).
% 6.35/1.19  fof(f2,axiom,(
% 6.35/1.19    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.35/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 6.35/1.19  fof(f4499,plain,(
% 6.35/1.19    ( ! [X1] : (~r2_hidden(sK2,X1) | k1_xboole_0 = k4_xboole_0(sK0,X1)) ) | ~spl6_4),
% 6.35/1.19    inference(superposition,[],[f41,f74])).
% 6.35/1.19  fof(f74,plain,(
% 6.35/1.19    sK0 = k1_tarski(sK2) | ~spl6_4),
% 6.35/1.19    inference(avatar_component_clause,[],[f73])).
% 6.35/1.19  fof(f73,plain,(
% 6.35/1.19    spl6_4 <=> sK0 = k1_tarski(sK2)),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 6.35/1.19  fof(f41,plain,(
% 6.35/1.19    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 6.35/1.19    inference(cnf_transformation,[],[f20])).
% 6.35/1.19  fof(f20,plain,(
% 6.35/1.19    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 6.35/1.19    inference(nnf_transformation,[],[f5])).
% 6.35/1.19  fof(f5,axiom,(
% 6.35/1.19    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 6.35/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 6.35/1.19  fof(f71,plain,(
% 6.35/1.19    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | spl6_3),
% 6.35/1.19    inference(avatar_component_clause,[],[f69])).
% 6.35/1.19  fof(f69,plain,(
% 6.35/1.19    spl6_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 6.35/1.19  fof(f4472,plain,(
% 6.35/1.19    ~spl6_29 | ~spl6_1 | spl6_2 | ~spl6_3 | spl6_49 | ~spl6_50),
% 6.35/1.19    inference(avatar_split_clause,[],[f2888,f2655,f2650,f69,f64,f60,f718])).
% 6.35/1.19  fof(f718,plain,(
% 6.35/1.19    spl6_29 <=> sK1 = sK4(sK1,sK2,sK0)),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 6.35/1.19  fof(f60,plain,(
% 6.35/1.19    spl6_1 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 6.35/1.19  fof(f64,plain,(
% 6.35/1.19    spl6_2 <=> sK0 = k2_tarski(sK1,sK2)),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 6.35/1.19  fof(f2650,plain,(
% 6.35/1.19    spl6_49 <=> sK2 = sK5(sK0,sK2)),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 6.35/1.19  fof(f2655,plain,(
% 6.35/1.19    spl6_50 <=> r2_hidden(sK5(sK0,sK2),sK0)),
% 6.35/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 6.35/1.19  fof(f2888,plain,(
% 6.35/1.19    sK1 != sK4(sK1,sK2,sK0) | (~spl6_1 | spl6_2 | ~spl6_3 | spl6_49 | ~spl6_50)),
% 6.35/1.19    inference(trivial_inequality_removal,[],[f2882])).
% 6.35/1.19  fof(f2882,plain,(
% 6.35/1.19    sK1 != sK4(sK1,sK2,sK0) | sK0 != sK0 | (~spl6_1 | spl6_2 | ~spl6_3 | spl6_49 | ~spl6_50)),
% 6.35/1.19    inference(resolution,[],[f2858,f2375])).
% 6.35/1.19  fof(f2375,plain,(
% 6.35/1.19    ( ! [X1] : (~r2_hidden(sK1,X1) | sK1 != sK4(sK1,sK2,X1) | sK0 != X1) ) | spl6_2),
% 6.35/1.19    inference(inner_rewriting,[],[f2373])).
% 6.35/1.19  fof(f2373,plain,(
% 6.35/1.19    ( ! [X1] : (sK0 != X1 | sK1 != sK4(sK1,sK2,X1) | ~r2_hidden(sK4(sK1,sK2,X1),X1)) ) | spl6_2),
% 6.35/1.19    inference(superposition,[],[f66,f46])).
% 6.35/1.19  fof(f46,plain,(
% 6.35/1.19    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) != X0 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 6.35/1.19    inference(cnf_transformation,[],[f25])).
% 6.35/1.19  fof(f66,plain,(
% 6.35/1.19    sK0 != k2_tarski(sK1,sK2) | spl6_2),
% 6.35/1.19    inference(avatar_component_clause,[],[f64])).
% 6.35/1.19  fof(f2858,plain,(
% 6.35/1.19    r2_hidden(sK1,sK0) | (~spl6_1 | ~spl6_3 | spl6_49 | ~spl6_50)),
% 6.35/1.19    inference(superposition,[],[f2657,f2833])).
% 6.35/1.19  fof(f2833,plain,(
% 6.35/1.19    sK1 = sK5(sK0,sK2) | (~spl6_1 | ~spl6_3 | spl6_49 | ~spl6_50)),
% 6.35/1.19    inference(subsumption_resolution,[],[f2826,f2652])).
% 6.35/1.19  fof(f2652,plain,(
% 6.35/1.19    sK2 != sK5(sK0,sK2) | spl6_49),
% 6.35/1.19    inference(avatar_component_clause,[],[f2650])).
% 6.35/1.19  fof(f2826,plain,(
% 6.35/1.19    sK2 = sK5(sK0,sK2) | sK1 = sK5(sK0,sK2) | (~spl6_1 | ~spl6_3 | ~spl6_50)),
% 6.35/1.19    inference(resolution,[],[f2693,f57])).
% 6.35/1.19  fof(f57,plain,(
% 6.35/1.19    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 6.35/1.19    inference(equality_resolution,[],[f42])).
% 6.35/1.19  fof(f42,plain,(
% 6.35/1.19    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 6.35/1.19    inference(cnf_transformation,[],[f25])).
% 6.35/1.19  fof(f2693,plain,(
% 6.35/1.19    r2_hidden(sK5(sK0,sK2),k2_tarski(sK1,sK2)) | (~spl6_1 | ~spl6_3 | ~spl6_50)),
% 6.35/1.19    inference(resolution,[],[f2678,f2657])).
% 6.35/1.19  fof(f2678,plain,(
% 6.35/1.19    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(X3,k2_tarski(sK1,sK2))) ) | (~spl6_1 | ~spl6_3)),
% 6.35/1.19    inference(subsumption_resolution,[],[f2673,f2352])).
% 6.35/1.19  fof(f2352,plain,(
% 6.35/1.19    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) ) | ~spl6_1),
% 6.35/1.19    inference(subsumption_resolution,[],[f2345,f2344])).
% 6.35/1.19  fof(f2344,plain,(
% 6.35/1.19    ( ! [X5] : (~r2_hidden(X5,sK0) | ~r2_hidden(X5,k1_xboole_0)) ) | ~spl6_1),
% 6.35/1.19    inference(superposition,[],[f51,f61])).
% 6.35/1.19  fof(f61,plain,(
% 6.35/1.19    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl6_1),
% 6.35/1.19    inference(avatar_component_clause,[],[f60])).
% 6.35/1.19  fof(f51,plain,(
% 6.35/1.19    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.35/1.19    inference(equality_resolution,[],[f35])).
% 6.35/1.19  fof(f35,plain,(
% 6.35/1.19    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.35/1.19    inference(cnf_transformation,[],[f19])).
% 6.35/1.19  fof(f19,plain,(
% 6.35/1.19    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.35/1.19    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 6.35/1.19  fof(f18,plain,(
% 6.35/1.19    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 6.35/1.19    introduced(choice_axiom,[])).
% 6.35/1.20  fof(f17,plain,(
% 6.35/1.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.35/1.20    inference(rectify,[],[f16])).
% 6.35/1.20  fof(f16,plain,(
% 6.35/1.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.35/1.20    inference(flattening,[],[f15])).
% 6.35/1.20  fof(f15,plain,(
% 6.35/1.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.35/1.20    inference(nnf_transformation,[],[f1])).
% 6.35/1.20  fof(f1,axiom,(
% 6.35/1.20    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.35/1.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.35/1.20  fof(f2345,plain,(
% 6.35/1.20    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(X6,sK0)) ) | ~spl6_1),
% 6.35/1.20    inference(superposition,[],[f52,f61])).
% 6.35/1.20  fof(f52,plain,(
% 6.35/1.20    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.35/1.20    inference(equality_resolution,[],[f34])).
% 6.35/1.20  fof(f34,plain,(
% 6.35/1.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.35/1.20    inference(cnf_transformation,[],[f19])).
% 6.35/1.20  fof(f2673,plain,(
% 6.35/1.20    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k2_tarski(sK1,sK2)) | ~r2_hidden(X3,sK0)) ) | ~spl6_3),
% 6.35/1.20    inference(superposition,[],[f50,f70])).
% 6.35/1.20  fof(f70,plain,(
% 6.35/1.20    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl6_3),
% 6.35/1.20    inference(avatar_component_clause,[],[f69])).
% 6.35/1.20  fof(f50,plain,(
% 6.35/1.20    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 6.35/1.20    inference(equality_resolution,[],[f36])).
% 6.35/1.20  fof(f36,plain,(
% 6.35/1.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 6.35/1.20    inference(cnf_transformation,[],[f19])).
% 6.35/1.20  fof(f2657,plain,(
% 6.35/1.20    r2_hidden(sK5(sK0,sK2),sK0) | ~spl6_50),
% 6.35/1.20    inference(avatar_component_clause,[],[f2655])).
% 6.35/1.20  fof(f4438,plain,(
% 6.35/1.20    spl6_29 | ~spl6_1 | ~spl6_3 | ~spl6_32 | spl6_33),
% 6.35/1.20    inference(avatar_split_clause,[],[f4433,f741,f737,f69,f60,f718])).
% 6.35/1.20  fof(f737,plain,(
% 6.35/1.20    spl6_32 <=> r2_hidden(sK4(sK1,sK2,sK0),sK0)),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 6.35/1.20  fof(f741,plain,(
% 6.35/1.20    spl6_33 <=> sK2 = sK4(sK1,sK2,sK0)),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 6.35/1.20  fof(f4433,plain,(
% 6.35/1.20    sK1 = sK4(sK1,sK2,sK0) | (~spl6_1 | ~spl6_3 | ~spl6_32 | spl6_33)),
% 6.35/1.20    inference(subsumption_resolution,[],[f4421,f742])).
% 6.35/1.20  fof(f742,plain,(
% 6.35/1.20    sK2 != sK4(sK1,sK2,sK0) | spl6_33),
% 6.35/1.20    inference(avatar_component_clause,[],[f741])).
% 6.35/1.20  fof(f4421,plain,(
% 6.35/1.20    sK2 = sK4(sK1,sK2,sK0) | sK1 = sK4(sK1,sK2,sK0) | (~spl6_1 | ~spl6_3 | ~spl6_32)),
% 6.35/1.20    inference(resolution,[],[f3334,f57])).
% 6.35/1.20  fof(f3334,plain,(
% 6.35/1.20    r2_hidden(sK4(sK1,sK2,sK0),k2_tarski(sK1,sK2)) | (~spl6_1 | ~spl6_3 | ~spl6_32)),
% 6.35/1.20    inference(resolution,[],[f739,f2678])).
% 6.35/1.20  fof(f739,plain,(
% 6.35/1.20    r2_hidden(sK4(sK1,sK2,sK0),sK0) | ~spl6_32),
% 6.35/1.20    inference(avatar_component_clause,[],[f737])).
% 6.35/1.20  fof(f3072,plain,(
% 6.35/1.20    spl6_44 | ~spl6_1 | ~spl6_3 | spl6_5 | spl6_7 | spl6_43),
% 6.35/1.20    inference(avatar_split_clause,[],[f3071,f1506,f88,f78,f69,f60,f1510])).
% 6.35/1.20  fof(f1510,plain,(
% 6.35/1.20    spl6_44 <=> sK2 = sK5(sK0,sK1)),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 6.35/1.20  fof(f78,plain,(
% 6.35/1.20    spl6_5 <=> sK0 = k1_tarski(sK1)),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 6.35/1.20  fof(f88,plain,(
% 6.35/1.20    spl6_7 <=> k1_xboole_0 = sK0),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 6.35/1.20  fof(f1506,plain,(
% 6.35/1.20    spl6_43 <=> sK1 = sK5(sK0,sK1)),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 6.35/1.20  fof(f3071,plain,(
% 6.35/1.20    sK2 = sK5(sK0,sK1) | (~spl6_1 | ~spl6_3 | spl6_5 | spl6_7 | spl6_43)),
% 6.35/1.20    inference(subsumption_resolution,[],[f3042,f1507])).
% 6.35/1.20  fof(f1507,plain,(
% 6.35/1.20    sK1 != sK5(sK0,sK1) | spl6_43),
% 6.35/1.20    inference(avatar_component_clause,[],[f1506])).
% 6.35/1.20  fof(f3042,plain,(
% 6.35/1.20    sK2 = sK5(sK0,sK1) | sK1 = sK5(sK0,sK1) | (~spl6_1 | ~spl6_3 | spl6_5 | spl6_7)),
% 6.35/1.20    inference(resolution,[],[f2708,f57])).
% 6.35/1.20  fof(f2708,plain,(
% 6.35/1.20    r2_hidden(sK5(sK0,sK1),k2_tarski(sK1,sK2)) | (~spl6_1 | ~spl6_3 | spl6_5 | spl6_7)),
% 6.35/1.20    inference(resolution,[],[f2707,f2678])).
% 6.35/1.20  fof(f2707,plain,(
% 6.35/1.20    r2_hidden(sK5(sK0,sK1),sK0) | (spl6_5 | spl6_7)),
% 6.35/1.20    inference(subsumption_resolution,[],[f2706,f90])).
% 6.35/1.20  fof(f90,plain,(
% 6.35/1.20    k1_xboole_0 != sK0 | spl6_7),
% 6.35/1.20    inference(avatar_component_clause,[],[f88])).
% 6.35/1.20  fof(f2706,plain,(
% 6.35/1.20    r2_hidden(sK5(sK0,sK1),sK0) | k1_xboole_0 = sK0 | spl6_5),
% 6.35/1.20    inference(equality_resolution,[],[f2662])).
% 6.35/1.20  fof(f2662,plain,(
% 6.35/1.20    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(X0,sK1),X0) | k1_xboole_0 = X0) ) | spl6_5),
% 6.35/1.20    inference(superposition,[],[f80,f48])).
% 6.35/1.20  fof(f48,plain,(
% 6.35/1.20    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 6.35/1.20    inference(cnf_transformation,[],[f27])).
% 6.35/1.20  fof(f27,plain,(
% 6.35/1.20    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 6.35/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f10,f26])).
% 6.35/1.20  fof(f26,plain,(
% 6.35/1.20    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 6.35/1.20    introduced(choice_axiom,[])).
% 6.35/1.20  fof(f10,plain,(
% 6.35/1.20    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 6.35/1.20    inference(ennf_transformation,[],[f6])).
% 6.35/1.20  fof(f6,axiom,(
% 6.35/1.20    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 6.35/1.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 6.35/1.20  fof(f80,plain,(
% 6.35/1.20    sK0 != k1_tarski(sK1) | spl6_5),
% 6.35/1.20    inference(avatar_component_clause,[],[f78])).
% 6.35/1.20  fof(f3070,plain,(
% 6.35/1.20    spl6_32 | spl6_33 | spl6_2 | spl6_29),
% 6.35/1.20    inference(avatar_split_clause,[],[f3069,f718,f64,f741,f737])).
% 6.35/1.20  fof(f3069,plain,(
% 6.35/1.20    sK2 = sK4(sK1,sK2,sK0) | r2_hidden(sK4(sK1,sK2,sK0),sK0) | (spl6_2 | spl6_29)),
% 6.35/1.20    inference(subsumption_resolution,[],[f734,f66])).
% 6.35/1.20  fof(f734,plain,(
% 6.35/1.20    sK0 = k2_tarski(sK1,sK2) | sK2 = sK4(sK1,sK2,sK0) | r2_hidden(sK4(sK1,sK2,sK0),sK0) | spl6_29),
% 6.35/1.20    inference(trivial_inequality_removal,[],[f732])).
% 6.35/1.20  fof(f732,plain,(
% 6.35/1.20    sK1 != sK1 | sK0 = k2_tarski(sK1,sK2) | sK2 = sK4(sK1,sK2,sK0) | r2_hidden(sK4(sK1,sK2,sK0),sK0) | spl6_29),
% 6.35/1.20    inference(superposition,[],[f720,f45])).
% 6.35/1.20  fof(f45,plain,(
% 6.35/1.20    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 6.35/1.20    inference(cnf_transformation,[],[f25])).
% 6.35/1.20  fof(f720,plain,(
% 6.35/1.20    sK1 != sK4(sK1,sK2,sK0) | spl6_29),
% 6.35/1.20    inference(avatar_component_clause,[],[f718])).
% 6.35/1.20  fof(f2715,plain,(
% 6.35/1.20    ~spl6_43 | spl6_5 | spl6_7),
% 6.35/1.20    inference(avatar_split_clause,[],[f2714,f88,f78,f1506])).
% 6.35/1.20  fof(f2714,plain,(
% 6.35/1.20    sK1 != sK5(sK0,sK1) | (spl6_5 | spl6_7)),
% 6.35/1.20    inference(subsumption_resolution,[],[f2713,f90])).
% 6.35/1.20  fof(f2713,plain,(
% 6.35/1.20    sK1 != sK5(sK0,sK1) | k1_xboole_0 = sK0 | spl6_5),
% 6.35/1.20    inference(equality_resolution,[],[f2663])).
% 6.35/1.20  fof(f2663,plain,(
% 6.35/1.20    ( ! [X1] : (sK0 != X1 | sK1 != sK5(X1,sK1) | k1_xboole_0 = X1) ) | spl6_5),
% 6.35/1.20    inference(superposition,[],[f80,f49])).
% 6.35/1.20  fof(f49,plain,(
% 6.35/1.20    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 6.35/1.20    inference(cnf_transformation,[],[f27])).
% 6.35/1.20  fof(f2660,plain,(
% 6.35/1.20    ~spl6_1 | spl6_6),
% 6.35/1.20    inference(avatar_contradiction_clause,[],[f2659])).
% 6.35/1.20  fof(f2659,plain,(
% 6.35/1.20    $false | (~spl6_1 | spl6_6)),
% 6.35/1.20    inference(subsumption_resolution,[],[f86,f2481])).
% 6.35/1.20  fof(f2481,plain,(
% 6.35/1.20    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) ) | ~spl6_1),
% 6.35/1.20    inference(resolution,[],[f2351,f2354])).
% 6.35/1.20  fof(f2354,plain,(
% 6.35/1.20    ( ! [X2,X1] : (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))) ) | ~spl6_1),
% 6.35/1.20    inference(resolution,[],[f2352,f52])).
% 6.35/1.20  fof(f2351,plain,(
% 6.35/1.20    ( ! [X1] : (r2_hidden(sK3(sK0,sK0,X1),X1) | k1_xboole_0 = X1) ) | ~spl6_1),
% 6.35/1.20    inference(subsumption_resolution,[],[f2334,f2333])).
% 6.35/1.20  fof(f2333,plain,(
% 6.35/1.20    ( ! [X0] : (r2_hidden(sK3(sK0,sK0,X0),sK0) | k1_xboole_0 = X0 | r2_hidden(sK3(sK0,sK0,X0),X0)) ) | ~spl6_1),
% 6.35/1.20    inference(superposition,[],[f61,f37])).
% 6.35/1.20  fof(f37,plain,(
% 6.35/1.20    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 6.35/1.20    inference(cnf_transformation,[],[f19])).
% 6.35/1.20  fof(f2334,plain,(
% 6.35/1.20    ( ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(sK3(sK0,sK0,X1),sK0) | r2_hidden(sK3(sK0,sK0,X1),X1)) ) | ~spl6_1),
% 6.35/1.20    inference(superposition,[],[f61,f38])).
% 6.35/1.20  fof(f38,plain,(
% 6.35/1.20    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 6.35/1.20    inference(cnf_transformation,[],[f19])).
% 6.35/1.20  fof(f86,plain,(
% 6.35/1.20    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) | spl6_6),
% 6.35/1.20    inference(avatar_component_clause,[],[f84])).
% 6.35/1.20  fof(f84,plain,(
% 6.35/1.20    spl6_6 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2))),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 6.35/1.20  fof(f2658,plain,(
% 6.35/1.20    spl6_7 | spl6_50 | spl6_4),
% 6.35/1.20    inference(avatar_split_clause,[],[f657,f73,f2655,f88])).
% 6.35/1.20  fof(f657,plain,(
% 6.35/1.20    r2_hidden(sK5(sK0,sK2),sK0) | k1_xboole_0 = sK0 | spl6_4),
% 6.35/1.20    inference(equality_resolution,[],[f594])).
% 6.35/1.20  fof(f594,plain,(
% 6.35/1.20    ( ! [X0] : (sK0 != X0 | r2_hidden(sK5(X0,sK2),X0) | k1_xboole_0 = X0) ) | spl6_4),
% 6.35/1.20    inference(superposition,[],[f75,f48])).
% 6.35/1.20  fof(f75,plain,(
% 6.35/1.20    sK0 != k1_tarski(sK2) | spl6_4),
% 6.35/1.20    inference(avatar_component_clause,[],[f73])).
% 6.35/1.20  fof(f2653,plain,(
% 6.35/1.20    spl6_7 | ~spl6_49 | spl6_4),
% 6.35/1.20    inference(avatar_split_clause,[],[f662,f73,f2650,f88])).
% 6.35/1.20  fof(f662,plain,(
% 6.35/1.20    sK2 != sK5(sK0,sK2) | k1_xboole_0 = sK0 | spl6_4),
% 6.35/1.20    inference(equality_resolution,[],[f595])).
% 6.35/1.20  fof(f595,plain,(
% 6.35/1.20    ( ! [X1] : (sK0 != X1 | sK2 != sK5(X1,sK2) | k1_xboole_0 = X1) ) | spl6_4),
% 6.35/1.20    inference(superposition,[],[f75,f49])).
% 6.35/1.20  fof(f2643,plain,(
% 6.35/1.20    spl6_3 | ~spl6_5),
% 6.35/1.20    inference(avatar_contradiction_clause,[],[f2642])).
% 6.35/1.20  fof(f2642,plain,(
% 6.35/1.20    $false | (spl6_3 | ~spl6_5)),
% 6.35/1.20    inference(trivial_inequality_removal,[],[f2627])).
% 6.35/1.20  fof(f2627,plain,(
% 6.35/1.20    k1_xboole_0 != k1_xboole_0 | (spl6_3 | ~spl6_5)),
% 6.35/1.20    inference(superposition,[],[f71,f2465])).
% 6.35/1.20  fof(f2465,plain,(
% 6.35/1.20    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,X9))) ) | ~spl6_5),
% 6.35/1.20    inference(resolution,[],[f2329,f56])).
% 6.35/1.20  fof(f56,plain,(
% 6.35/1.20    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 6.35/1.20    inference(equality_resolution,[],[f55])).
% 6.35/1.20  fof(f55,plain,(
% 6.35/1.20    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 6.35/1.20    inference(equality_resolution,[],[f43])).
% 6.35/1.20  fof(f43,plain,(
% 6.35/1.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.35/1.20    inference(cnf_transformation,[],[f25])).
% 6.35/1.20  fof(f2329,plain,(
% 6.35/1.20    ( ! [X4] : (~r2_hidden(sK1,X4) | k1_xboole_0 = k4_xboole_0(sK0,X4)) ) | ~spl6_5),
% 6.35/1.20    inference(superposition,[],[f41,f79])).
% 6.35/1.20  fof(f79,plain,(
% 6.35/1.20    sK0 = k1_tarski(sK1) | ~spl6_5),
% 6.35/1.20    inference(avatar_component_clause,[],[f78])).
% 6.35/1.20  fof(f2317,plain,(
% 6.35/1.20    spl6_5 | spl6_42 | spl6_7 | ~spl6_44),
% 6.35/1.20    inference(avatar_split_clause,[],[f2316,f1510,f88,f1448,f78])).
% 6.35/1.20  fof(f1448,plain,(
% 6.35/1.20    spl6_42 <=> r2_hidden(sK2,sK0)),
% 6.35/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 6.35/1.20  fof(f2316,plain,(
% 6.35/1.20    r2_hidden(sK2,sK0) | sK0 = k1_tarski(sK1) | (spl6_7 | ~spl6_44)),
% 6.35/1.20    inference(subsumption_resolution,[],[f1532,f90])).
% 6.35/1.20  fof(f1532,plain,(
% 6.35/1.20    r2_hidden(sK2,sK0) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | ~spl6_44),
% 6.35/1.20    inference(superposition,[],[f48,f1512])).
% 6.35/1.20  fof(f1512,plain,(
% 6.35/1.20    sK2 = sK5(sK0,sK1) | ~spl6_44),
% 6.35/1.20    inference(avatar_component_clause,[],[f1510])).
% 6.35/1.20  fof(f2295,plain,(
% 6.35/1.20    spl6_1),
% 6.35/1.20    inference(avatar_contradiction_clause,[],[f2294])).
% 6.35/1.20  fof(f2294,plain,(
% 6.35/1.20    $false | spl6_1),
% 6.35/1.20    inference(subsumption_resolution,[],[f2293,f149])).
% 6.35/1.20  fof(f149,plain,(
% 6.35/1.20    r2_hidden(sK3(sK0,sK0,k1_xboole_0),k1_xboole_0) | spl6_1),
% 6.35/1.20    inference(equality_resolution,[],[f96])).
% 6.35/1.20  fof(f96,plain,(
% 6.35/1.20    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK3(sK0,sK0,X1),X1)) ) | spl6_1),
% 6.35/1.20    inference(subsumption_resolution,[],[f94,f93])).
% 6.35/1.20  fof(f93,plain,(
% 6.35/1.20    ( ! [X0] : (r2_hidden(sK3(sK0,sK0,X0),sK0) | k1_xboole_0 != X0 | r2_hidden(sK3(sK0,sK0,X0),X0)) ) | spl6_1),
% 6.35/1.20    inference(superposition,[],[f62,f37])).
% 6.35/1.20  fof(f62,plain,(
% 6.35/1.20    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl6_1),
% 6.35/1.20    inference(avatar_component_clause,[],[f60])).
% 6.35/1.20  fof(f94,plain,(
% 6.35/1.20    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK3(sK0,sK0,X1),sK0) | r2_hidden(sK3(sK0,sK0,X1),X1)) ) | spl6_1),
% 6.35/1.20    inference(superposition,[],[f62,f38])).
% 6.35/1.20  fof(f2293,plain,(
% 6.35/1.20    ~r2_hidden(sK3(sK0,sK0,k1_xboole_0),k1_xboole_0) | spl6_1),
% 6.35/1.20    inference(condensation,[],[f2292])).
% 6.35/1.20  fof(f2292,plain,(
% 6.35/1.20    ( ! [X6] : (~r2_hidden(sK3(sK0,sK0,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) ) | spl6_1),
% 6.35/1.20    inference(superposition,[],[f308,f41])).
% 6.35/1.20  fof(f308,plain,(
% 6.35/1.20    ( ! [X0] : (~r2_hidden(sK3(sK0,sK0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ) | spl6_1),
% 6.35/1.20    inference(resolution,[],[f149,f51])).
% 6.35/1.20  fof(f1452,plain,(
% 6.35/1.20    ~spl6_42 | spl6_2 | ~spl6_33),
% 6.35/1.20    inference(avatar_split_clause,[],[f797,f741,f64,f1448])).
% 6.35/1.20  fof(f797,plain,(
% 6.35/1.20    sK0 = k2_tarski(sK1,sK2) | ~r2_hidden(sK2,sK0) | ~spl6_33),
% 6.35/1.20    inference(trivial_inequality_removal,[],[f794])).
% 6.35/1.20  fof(f794,plain,(
% 6.35/1.20    sK2 != sK2 | sK0 = k2_tarski(sK1,sK2) | ~r2_hidden(sK2,sK0) | ~spl6_33),
% 6.35/1.20    inference(superposition,[],[f47,f743])).
% 6.35/1.20  fof(f743,plain,(
% 6.35/1.20    sK2 = sK4(sK1,sK2,sK0) | ~spl6_33),
% 6.35/1.20    inference(avatar_component_clause,[],[f741])).
% 6.35/1.20  fof(f47,plain,(
% 6.35/1.20    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) != X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 6.35/1.20    inference(cnf_transformation,[],[f25])).
% 6.35/1.20  fof(f92,plain,(
% 6.35/1.20    spl6_3 | spl6_7 | spl6_5 | spl6_4 | spl6_2),
% 6.35/1.20    inference(avatar_split_clause,[],[f28,f64,f73,f78,f88,f69])).
% 6.35/1.20  fof(f28,plain,(
% 6.35/1.20    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 6.35/1.20    inference(cnf_transformation,[],[f14])).
% 6.35/1.20  fof(f14,plain,(
% 6.35/1.20    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 6.35/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 6.35/1.20  fof(f13,plain,(
% 6.35/1.20    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 6.35/1.20    introduced(choice_axiom,[])).
% 6.35/1.20  fof(f12,plain,(
% 6.35/1.20    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 6.35/1.20    inference(flattening,[],[f11])).
% 6.35/1.20  fof(f11,plain,(
% 6.35/1.20    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 6.35/1.20    inference(nnf_transformation,[],[f9])).
% 6.35/1.20  fof(f9,plain,(
% 6.35/1.20    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 6.35/1.20    inference(ennf_transformation,[],[f8])).
% 6.35/1.20  fof(f8,negated_conjecture,(
% 6.35/1.20    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 6.35/1.20    inference(negated_conjecture,[],[f7])).
% 6.35/1.20  fof(f7,conjecture,(
% 6.35/1.20    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 6.35/1.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 6.35/1.20  fof(f91,plain,(
% 6.35/1.20    ~spl6_6 | ~spl6_7),
% 6.35/1.20    inference(avatar_split_clause,[],[f82,f88,f84])).
% 6.35/1.20  fof(f82,plain,(
% 6.35/1.20    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2))),
% 6.35/1.20    inference(inner_rewriting,[],[f29])).
% 6.35/1.20  fof(f29,plain,(
% 6.35/1.20    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 6.35/1.20    inference(cnf_transformation,[],[f14])).
% 6.35/1.20  fof(f81,plain,(
% 6.35/1.20    ~spl6_3 | ~spl6_5),
% 6.35/1.20    inference(avatar_split_clause,[],[f30,f78,f69])).
% 6.35/1.20  fof(f30,plain,(
% 6.35/1.20    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 6.35/1.20    inference(cnf_transformation,[],[f14])).
% 6.35/1.20  fof(f76,plain,(
% 6.35/1.20    ~spl6_3 | ~spl6_4),
% 6.35/1.20    inference(avatar_split_clause,[],[f31,f73,f69])).
% 6.35/1.20  fof(f31,plain,(
% 6.35/1.20    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 6.35/1.20    inference(cnf_transformation,[],[f14])).
% 6.35/1.20  fof(f67,plain,(
% 6.35/1.20    ~spl6_1 | ~spl6_2),
% 6.35/1.20    inference(avatar_split_clause,[],[f58,f64,f60])).
% 6.35/1.20  fof(f58,plain,(
% 6.35/1.20    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 6.35/1.20    inference(inner_rewriting,[],[f32])).
% 6.35/1.20  fof(f32,plain,(
% 6.35/1.20    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 6.35/1.20    inference(cnf_transformation,[],[f14])).
% 6.35/1.20  % SZS output end Proof for theBenchmark
% 6.35/1.20  % (24514)------------------------------
% 6.35/1.20  % (24514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.35/1.20  % (24514)Termination reason: Refutation
% 6.35/1.20  
% 6.35/1.20  % (24514)Memory used [KB]: 12281
% 6.35/1.20  % (24514)Time elapsed: 0.752 s
% 6.35/1.20  % (24514)------------------------------
% 6.35/1.20  % (24514)------------------------------
% 6.35/1.20  % (24499)Success in time 0.843 s
%------------------------------------------------------------------------------
