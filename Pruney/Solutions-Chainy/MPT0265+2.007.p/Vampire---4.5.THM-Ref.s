%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:26 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 157 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  333 ( 808 expanded)
%              Number of equality atoms :  114 ( 339 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f443,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f90,f260,f267,f353,f405,f426,f430,f439,f440,f442])).

fof(f442,plain,
    ( sK0 != sK2
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f440,plain,
    ( sK2 != sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f439,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | spl6_16 ),
    inference(unit_resulting_resolution,[],[f65,f425])).

fof(f425,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl6_16
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f65,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f430,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f67,f421])).

fof(f421,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl6_15
  <=> r2_hidden(sK0,k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f67,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f426,plain,
    ( ~ spl6_1
    | ~ spl6_15
    | ~ spl6_16
    | spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f416,f264,f87,f423,f419,f73])).

fof(f73,plain,
    ( spl6_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f87,plain,
    ( spl6_4
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f264,plain,
    ( spl6_8
  <=> sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f416,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | spl6_4
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f415,f266])).

fof(f266,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f264])).

fof(f415,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f414,f266])).

fof(f414,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2))
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f413,f266])).

fof(f413,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2))
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f397])).

fof(f397,plain,
    ( ! [X129] :
        ( k2_tarski(sK0,sK0) != X129
        | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X129),sK1)
        | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X129),k2_tarski(sK0,sK2))
        | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X129),X129) )
    | spl6_4 ),
    inference(superposition,[],[f89,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f89,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f405,plain,
    ( spl6_13
    | spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f354,f350,f264,f402])).

fof(f402,plain,
    ( spl6_13
  <=> sK2 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f350,plain,
    ( spl6_12
  <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f354,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | sK2 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | ~ spl6_12 ),
    inference(resolution,[],[f352,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f352,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f350])).

fof(f353,plain,
    ( spl6_6
    | spl6_12
    | spl6_4 ),
    inference(avatar_split_clause,[],[f347,f87,f350,f253])).

fof(f253,plain,
    ( spl6_6
  <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f347,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2))
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f306])).

fof(f306,plain,
    ( ! [X121] :
        ( k2_tarski(sK0,sK0) != X121
        | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X121),k2_tarski(sK0,sK2))
        | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X121),X121) )
    | spl6_4 ),
    inference(superposition,[],[f89,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f267,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f262,f253,f264])).

fof(f262,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))
    | ~ spl6_6 ),
    inference(resolution,[],[f255,f68])).

fof(f255,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f253])).

fof(f260,plain,
    ( spl6_6
    | spl6_7
    | spl6_4 ),
    inference(avatar_split_clause,[],[f251,f87,f257,f253])).

fof(f257,plain,
    ( spl6_7
  <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f251,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f247])).

fof(f247,plain,
    ( ! [X113] :
        ( k2_tarski(sK0,sK0) != X113
        | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X113),sK1)
        | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X113),X113) )
    | spl6_4 ),
    inference(superposition,[],[f89,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f53,f87])).

fof(f53,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f31,f46,f38])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
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

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f85,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f30,f82,f78])).

fof(f78,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f82,plain,
    ( spl6_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f30,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:13:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (9737)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (9733)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (9731)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (9753)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (9744)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (9745)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (9734)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (9732)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (9745)Refutation not found, incomplete strategy% (9745)------------------------------
% 0.22/0.52  % (9745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9745)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9745)Memory used [KB]: 1663
% 0.22/0.52  % (9745)Time elapsed: 0.107 s
% 0.22/0.52  % (9745)------------------------------
% 0.22/0.52  % (9745)------------------------------
% 0.22/0.52  % (9757)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (9755)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (9736)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9749)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (9739)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (9748)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (9741)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (9747)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (9742)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (9747)Refutation not found, incomplete strategy% (9747)------------------------------
% 0.22/0.54  % (9747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9747)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9747)Memory used [KB]: 10618
% 0.22/0.54  % (9747)Time elapsed: 0.133 s
% 0.22/0.54  % (9747)------------------------------
% 0.22/0.54  % (9747)------------------------------
% 0.22/0.54  % (9735)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (9740)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (9759)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.54  % (9751)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (9758)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (9743)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.55  % (9756)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (9748)Refutation not found, incomplete strategy% (9748)------------------------------
% 1.39/0.55  % (9748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (9748)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (9748)Memory used [KB]: 1663
% 1.39/0.55  % (9748)Time elapsed: 0.150 s
% 1.39/0.55  % (9748)------------------------------
% 1.39/0.55  % (9748)------------------------------
% 1.39/0.55  % (9750)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.56  % (9760)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.54/0.57  % (9752)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.54/0.58  % (9746)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.54/0.58  % (9738)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.54/0.59  % (9754)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.00/0.63  % (9754)Refutation found. Thanks to Tanya!
% 2.00/0.63  % SZS status Theorem for theBenchmark
% 2.00/0.63  % SZS output start Proof for theBenchmark
% 2.00/0.63  fof(f443,plain,(
% 2.00/0.63    $false),
% 2.00/0.63    inference(avatar_sat_refutation,[],[f76,f85,f90,f260,f267,f353,f405,f426,f430,f439,f440,f442])).
% 2.00/0.63  fof(f442,plain,(
% 2.00/0.63    sK0 != sK2 | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2))),
% 2.00/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.00/0.63  fof(f440,plain,(
% 2.00/0.63    sK2 != sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | r2_hidden(sK2,sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1)),
% 2.00/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.00/0.63  fof(f439,plain,(
% 2.00/0.63    spl6_16),
% 2.00/0.63    inference(avatar_contradiction_clause,[],[f434])).
% 2.00/0.63  fof(f434,plain,(
% 2.00/0.63    $false | spl6_16),
% 2.00/0.63    inference(unit_resulting_resolution,[],[f65,f425])).
% 2.00/0.63  fof(f425,plain,(
% 2.00/0.63    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl6_16),
% 2.00/0.63    inference(avatar_component_clause,[],[f423])).
% 2.00/0.63  fof(f423,plain,(
% 2.00/0.63    spl6_16 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.00/0.63  fof(f65,plain,(
% 2.00/0.63    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.00/0.63    inference(equality_resolution,[],[f64])).
% 2.00/0.63  fof(f64,plain,(
% 2.00/0.63    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.00/0.63    inference(equality_resolution,[],[f42])).
% 2.00/0.63  fof(f42,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.00/0.63    inference(cnf_transformation,[],[f23])).
% 2.00/0.63  fof(f23,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.00/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 2.00/0.63  fof(f22,plain,(
% 2.00/0.63    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.00/0.63    introduced(choice_axiom,[])).
% 2.00/0.63  fof(f21,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.00/0.63    inference(rectify,[],[f20])).
% 2.00/0.63  fof(f20,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.00/0.63    inference(flattening,[],[f19])).
% 2.00/0.63  fof(f19,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.00/0.63    inference(nnf_transformation,[],[f5])).
% 2.00/0.63  fof(f5,axiom,(
% 2.00/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.00/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.00/0.63  fof(f430,plain,(
% 2.00/0.63    spl6_15),
% 2.00/0.63    inference(avatar_contradiction_clause,[],[f427])).
% 2.00/0.63  fof(f427,plain,(
% 2.00/0.63    $false | spl6_15),
% 2.00/0.63    inference(unit_resulting_resolution,[],[f67,f421])).
% 2.00/0.63  fof(f421,plain,(
% 2.00/0.63    ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | spl6_15),
% 2.00/0.63    inference(avatar_component_clause,[],[f419])).
% 2.00/0.63  fof(f419,plain,(
% 2.00/0.63    spl6_15 <=> r2_hidden(sK0,k2_tarski(sK0,sK2))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.00/0.63  fof(f67,plain,(
% 2.00/0.63    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.00/0.63    inference(equality_resolution,[],[f66])).
% 2.00/0.63  fof(f66,plain,(
% 2.00/0.63    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.00/0.63    inference(equality_resolution,[],[f41])).
% 2.00/0.63  fof(f41,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.00/0.63    inference(cnf_transformation,[],[f23])).
% 2.00/0.63  fof(f426,plain,(
% 2.00/0.63    ~spl6_1 | ~spl6_15 | ~spl6_16 | spl6_4 | ~spl6_8),
% 2.00/0.63    inference(avatar_split_clause,[],[f416,f264,f87,f423,f419,f73])).
% 2.00/0.63  fof(f73,plain,(
% 2.00/0.63    spl6_1 <=> r2_hidden(sK0,sK1)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.00/0.63  fof(f87,plain,(
% 2.00/0.63    spl6_4 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.00/0.63  fof(f264,plain,(
% 2.00/0.63    spl6_8 <=> sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.00/0.63  fof(f416,plain,(
% 2.00/0.63    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~r2_hidden(sK0,sK1) | (spl6_4 | ~spl6_8)),
% 2.00/0.63    inference(forward_demodulation,[],[f415,f266])).
% 2.00/0.63  fof(f266,plain,(
% 2.00/0.63    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | ~spl6_8),
% 2.00/0.63    inference(avatar_component_clause,[],[f264])).
% 2.00/0.63  fof(f415,plain,(
% 2.00/0.63    ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | (spl6_4 | ~spl6_8)),
% 2.00/0.63    inference(forward_demodulation,[],[f414,f266])).
% 2.00/0.63  fof(f414,plain,(
% 2.00/0.63    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2)) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | (spl6_4 | ~spl6_8)),
% 2.00/0.63    inference(forward_demodulation,[],[f413,f266])).
% 2.00/0.63  fof(f413,plain,(
% 2.00/0.63    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2)) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl6_4),
% 2.00/0.63    inference(equality_resolution,[],[f397])).
% 2.00/0.63  fof(f397,plain,(
% 2.00/0.63    ( ! [X129] : (k2_tarski(sK0,sK0) != X129 | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X129),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X129),k2_tarski(sK0,sK2)) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X129),X129)) ) | spl6_4),
% 2.00/0.63    inference(superposition,[],[f89,f54])).
% 2.00/0.63  fof(f54,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.00/0.63    inference(definition_unfolding,[],[f37,f38])).
% 2.00/0.63  fof(f38,plain,(
% 2.00/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.00/0.63    inference(cnf_transformation,[],[f4])).
% 2.00/0.63  fof(f4,axiom,(
% 2.00/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.00/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.00/0.63  fof(f37,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f18])).
% 2.00/0.63  fof(f18,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.00/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 2.00/0.64  fof(f17,plain,(
% 2.00/0.64    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.00/0.64    introduced(choice_axiom,[])).
% 2.00/0.64  fof(f16,plain,(
% 2.00/0.64    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.00/0.64    inference(rectify,[],[f15])).
% 2.00/0.64  fof(f15,plain,(
% 2.00/0.64    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.00/0.64    inference(flattening,[],[f14])).
% 2.00/0.64  fof(f14,plain,(
% 2.00/0.64    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.00/0.64    inference(nnf_transformation,[],[f2])).
% 2.00/0.64  fof(f2,axiom,(
% 2.00/0.64    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.00/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.00/0.64  fof(f89,plain,(
% 2.00/0.64    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl6_4),
% 2.00/0.64    inference(avatar_component_clause,[],[f87])).
% 2.00/0.64  fof(f405,plain,(
% 2.00/0.64    spl6_13 | spl6_8 | ~spl6_12),
% 2.00/0.64    inference(avatar_split_clause,[],[f354,f350,f264,f402])).
% 2.00/0.64  fof(f402,plain,(
% 2.00/0.64    spl6_13 <=> sK2 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0))),
% 2.00/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.00/0.64  fof(f350,plain,(
% 2.00/0.64    spl6_12 <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2))),
% 2.00/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.00/0.64  fof(f354,plain,(
% 2.00/0.64    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | sK2 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | ~spl6_12),
% 2.00/0.64    inference(resolution,[],[f352,f68])).
% 2.00/0.64  fof(f68,plain,(
% 2.00/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.00/0.64    inference(equality_resolution,[],[f40])).
% 2.00/0.64  fof(f40,plain,(
% 2.00/0.64    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.00/0.64    inference(cnf_transformation,[],[f23])).
% 2.00/0.64  fof(f352,plain,(
% 2.00/0.64    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2)) | ~spl6_12),
% 2.00/0.64    inference(avatar_component_clause,[],[f350])).
% 2.00/0.64  fof(f353,plain,(
% 2.00/0.64    spl6_6 | spl6_12 | spl6_4),
% 2.00/0.64    inference(avatar_split_clause,[],[f347,f87,f350,f253])).
% 2.00/0.64  fof(f253,plain,(
% 2.00/0.64    spl6_6 <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 2.00/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.00/0.64  fof(f347,plain,(
% 2.00/0.64    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl6_4),
% 2.00/0.64    inference(equality_resolution,[],[f306])).
% 2.00/0.64  fof(f306,plain,(
% 2.00/0.64    ( ! [X121] : (k2_tarski(sK0,sK0) != X121 | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X121),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X121),X121)) ) | spl6_4),
% 2.00/0.64    inference(superposition,[],[f89,f56])).
% 2.00/0.64  fof(f56,plain,(
% 2.00/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.00/0.64    inference(definition_unfolding,[],[f35,f38])).
% 2.00/0.64  fof(f35,plain,(
% 2.00/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.00/0.64    inference(cnf_transformation,[],[f18])).
% 2.00/0.64  fof(f267,plain,(
% 2.00/0.64    spl6_8 | ~spl6_6),
% 2.00/0.64    inference(avatar_split_clause,[],[f262,f253,f264])).
% 2.00/0.64  fof(f262,plain,(
% 2.00/0.64    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | ~spl6_6),
% 2.00/0.64    inference(duplicate_literal_removal,[],[f261])).
% 2.00/0.64  fof(f261,plain,(
% 2.00/0.64    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)) | ~spl6_6),
% 2.00/0.64    inference(resolution,[],[f255,f68])).
% 2.00/0.64  fof(f255,plain,(
% 2.00/0.64    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~spl6_6),
% 2.00/0.64    inference(avatar_component_clause,[],[f253])).
% 2.00/0.64  fof(f260,plain,(
% 2.00/0.64    spl6_6 | spl6_7 | spl6_4),
% 2.00/0.64    inference(avatar_split_clause,[],[f251,f87,f257,f253])).
% 2.00/0.64  fof(f257,plain,(
% 2.00/0.64    spl6_7 <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1)),
% 2.00/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.00/0.64  fof(f251,plain,(
% 2.00/0.64    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),sK1) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl6_4),
% 2.00/0.64    inference(equality_resolution,[],[f247])).
% 2.00/0.64  fof(f247,plain,(
% 2.00/0.64    ( ! [X113] : (k2_tarski(sK0,sK0) != X113 | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X113),sK1) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X113),X113)) ) | spl6_4),
% 2.00/0.64    inference(superposition,[],[f89,f55])).
% 2.00/0.64  fof(f55,plain,(
% 2.00/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.00/0.64    inference(definition_unfolding,[],[f36,f38])).
% 2.00/0.64  fof(f36,plain,(
% 2.00/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.00/0.64    inference(cnf_transformation,[],[f18])).
% 2.00/0.64  fof(f90,plain,(
% 2.00/0.64    ~spl6_4),
% 2.00/0.64    inference(avatar_split_clause,[],[f53,f87])).
% 2.00/0.64  fof(f53,plain,(
% 2.00/0.64    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 2.00/0.64    inference(definition_unfolding,[],[f31,f46,f38])).
% 2.00/0.64  fof(f46,plain,(
% 2.00/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.00/0.64    inference(cnf_transformation,[],[f6])).
% 2.00/0.64  fof(f6,axiom,(
% 2.00/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.00/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.00/0.64  fof(f31,plain,(
% 2.00/0.64    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 2.00/0.64    inference(cnf_transformation,[],[f13])).
% 2.00/0.64  fof(f13,plain,(
% 2.00/0.64    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1)),
% 2.00/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 2.00/0.64  fof(f12,plain,(
% 2.00/0.64    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1))),
% 2.00/0.64    introduced(choice_axiom,[])).
% 2.00/0.64  fof(f11,plain,(
% 2.00/0.64    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.00/0.64    inference(flattening,[],[f10])).
% 2.00/0.64  fof(f10,plain,(
% 2.00/0.64    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 2.00/0.64    inference(ennf_transformation,[],[f9])).
% 2.00/0.64  fof(f9,negated_conjecture,(
% 2.00/0.64    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.00/0.64    inference(negated_conjecture,[],[f8])).
% 2.00/0.64  fof(f8,conjecture,(
% 2.00/0.64    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.00/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 2.00/0.64  fof(f85,plain,(
% 2.00/0.64    ~spl6_2 | spl6_3),
% 2.00/0.64    inference(avatar_split_clause,[],[f30,f82,f78])).
% 2.00/0.64  fof(f78,plain,(
% 2.00/0.64    spl6_2 <=> r2_hidden(sK2,sK1)),
% 2.00/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.00/0.64  fof(f82,plain,(
% 2.00/0.64    spl6_3 <=> sK0 = sK2),
% 2.00/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.00/0.64  fof(f30,plain,(
% 2.00/0.64    sK0 = sK2 | ~r2_hidden(sK2,sK1)),
% 2.00/0.64    inference(cnf_transformation,[],[f13])).
% 2.00/0.64  fof(f76,plain,(
% 2.00/0.64    spl6_1),
% 2.00/0.64    inference(avatar_split_clause,[],[f29,f73])).
% 2.00/0.64  fof(f29,plain,(
% 2.00/0.64    r2_hidden(sK0,sK1)),
% 2.00/0.64    inference(cnf_transformation,[],[f13])).
% 2.00/0.64  % SZS output end Proof for theBenchmark
% 2.00/0.64  % (9754)------------------------------
% 2.00/0.64  % (9754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.64  % (9754)Termination reason: Refutation
% 2.00/0.64  
% 2.00/0.64  % (9754)Memory used [KB]: 11129
% 2.00/0.64  % (9754)Time elapsed: 0.133 s
% 2.00/0.64  % (9754)------------------------------
% 2.00/0.64  % (9754)------------------------------
% 2.00/0.65  % (9730)Success in time 0.284 s
%------------------------------------------------------------------------------
