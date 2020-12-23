%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:28 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 197 expanded)
%              Number of leaves         :   14 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 (1073 expanded)
%              Number of equality atoms :  131 ( 434 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f320,f371,f614,f658,f688,f697,f700])).

fof(f700,plain,
    ( spl5_8
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f274,f277])).

fof(f277,plain,
    ( ! [X1] : r2_hidden(sK0,X1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl5_9
  <=> ! [X1] : r2_hidden(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f274,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f697,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f691,f28])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f691,plain,
    ( sK0 = sK1
    | ~ spl5_8 ),
    inference(resolution,[],[f273,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f273,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f272])).

fof(f688,plain,
    ( ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f668,f28])).

fof(f668,plain,
    ( sK0 = sK1
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(resolution,[],[f664,f57])).

fof(f664,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f138,f370])).

fof(f370,plain,
    ( sK1 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl5_11
  <=> sK1 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f138,plain,
    ( r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_5
  <=> r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f658,plain,
    ( spl5_8
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f656,f53])).

fof(f53,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f656,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f655,f274])).

fof(f655,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f654,f29])).

fof(f29,plain,(
    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f654,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    | r2_hidden(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f637,f56])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f637,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    | r2_hidden(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_10 ),
    inference(superposition,[],[f35,f366])).

fof(f366,plain,
    ( sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl5_10
  <=> sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f614,plain,
    ( spl5_5
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f612,f56])).

fof(f612,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f611,f29])).

fof(f611,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f597,f592])).

fof(f592,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl5_5
    | ~ spl5_11 ),
    inference(superposition,[],[f137,f370])).

fof(f137,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f597,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl5_11 ),
    inference(superposition,[],[f34,f370])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f371,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f353,f162,f368,f364])).

fof(f162,plain,
    ( spl5_7
  <=> r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f353,plain,
    ( sK1 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f164,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f164,plain,
    ( r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f320,plain,
    ( spl5_9
    | ~ spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f319,f162,f136,f276])).

fof(f319,plain,
    ( ! [X1] : r2_hidden(sK0,X1)
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f310,f53])).

fof(f310,plain,
    ( ! [X1] :
        ( r2_hidden(sK0,X1)
        | ~ r2_hidden(sK0,k2_tarski(sK0,sK1)) )
    | ~ spl5_5
    | spl5_7 ),
    inference(resolution,[],[f290,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f290,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),X0))
    | ~ spl5_5
    | spl5_7 ),
    inference(forward_demodulation,[],[f281,f219])).

fof(f219,plain,
    ( sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f138,f57])).

fof(f281,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k2_tarski(sK0,sK1),X0))
    | spl5_7 ),
    inference(resolution,[],[f163,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f163,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f165,plain,
    ( spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f159,f162,f136])).

fof(f159,plain,
    ( r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1))
    | r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_tarski(sK0) != X0
      | r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),X0),k2_tarski(sK0,sK1))
      | r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),X0),X0) ) ),
    inference(superposition,[],[f29,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (24556)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (24553)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (24554)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (24557)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24559)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (24563)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (24580)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (24551)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (24565)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (24569)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (24552)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (24552)Refutation not found, incomplete strategy% (24552)------------------------------
% 0.21/0.53  % (24552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24569)Refutation not found, incomplete strategy% (24569)------------------------------
% 0.21/0.53  % (24569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24552)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24552)Memory used [KB]: 1663
% 0.21/0.53  % (24552)Time elapsed: 0.113 s
% 0.21/0.53  % (24552)------------------------------
% 0.21/0.53  % (24552)------------------------------
% 0.21/0.53  % (24561)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (24558)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (24567)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (24574)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (24578)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24578)Refutation not found, incomplete strategy% (24578)------------------------------
% 0.21/0.54  % (24578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24578)Memory used [KB]: 6268
% 0.21/0.54  % (24578)Time elapsed: 0.127 s
% 0.21/0.54  % (24578)------------------------------
% 0.21/0.54  % (24578)------------------------------
% 0.21/0.54  % (24569)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24569)Memory used [KB]: 1663
% 0.21/0.54  % (24569)Time elapsed: 0.120 s
% 0.21/0.54  % (24569)------------------------------
% 0.21/0.54  % (24569)------------------------------
% 0.21/0.54  % (24572)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (24555)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (24581)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24577)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (24576)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (24575)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (24560)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (24570)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (24562)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (24568)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (24573)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (24568)Refutation not found, incomplete strategy% (24568)------------------------------
% 0.21/0.55  % (24568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24568)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24568)Memory used [KB]: 10618
% 0.21/0.55  % (24568)Time elapsed: 0.149 s
% 0.21/0.55  % (24568)------------------------------
% 0.21/0.55  % (24568)------------------------------
% 0.21/0.55  % (24576)Refutation not found, incomplete strategy% (24576)------------------------------
% 0.21/0.55  % (24576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24576)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24576)Memory used [KB]: 10618
% 0.21/0.55  % (24576)Time elapsed: 0.142 s
% 0.21/0.55  % (24576)------------------------------
% 0.21/0.55  % (24576)------------------------------
% 0.21/0.55  % (24579)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (24566)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (24579)Refutation not found, incomplete strategy% (24579)------------------------------
% 0.21/0.56  % (24579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24579)Memory used [KB]: 6140
% 0.21/0.56  % (24579)Time elapsed: 0.149 s
% 0.21/0.56  % (24579)------------------------------
% 0.21/0.56  % (24579)------------------------------
% 0.21/0.56  % (24566)Refutation not found, incomplete strategy% (24566)------------------------------
% 0.21/0.56  % (24566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (24581)Refutation not found, incomplete strategy% (24581)------------------------------
% 1.49/0.56  % (24581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (24566)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (24566)Memory used [KB]: 1663
% 1.49/0.56  % (24566)Time elapsed: 0.151 s
% 1.49/0.56  % (24566)------------------------------
% 1.49/0.56  % (24566)------------------------------
% 1.49/0.56  % (24581)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (24581)Memory used [KB]: 1663
% 1.49/0.56  % (24581)Time elapsed: 0.148 s
% 1.49/0.56  % (24581)------------------------------
% 1.49/0.56  % (24581)------------------------------
% 1.49/0.56  % (24571)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (24570)Refutation not found, incomplete strategy% (24570)------------------------------
% 1.49/0.56  % (24570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (24570)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (24570)Memory used [KB]: 1663
% 1.49/0.56  % (24570)Time elapsed: 0.157 s
% 1.49/0.56  % (24570)------------------------------
% 1.49/0.56  % (24570)------------------------------
% 1.67/0.58  % (24563)Refutation found. Thanks to Tanya!
% 1.67/0.58  % SZS status Theorem for theBenchmark
% 1.67/0.59  % SZS output start Proof for theBenchmark
% 1.67/0.59  fof(f701,plain,(
% 1.67/0.59    $false),
% 1.67/0.59    inference(avatar_sat_refutation,[],[f165,f320,f371,f614,f658,f688,f697,f700])).
% 1.67/0.59  fof(f700,plain,(
% 1.67/0.59    spl5_8 | ~spl5_9),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f699])).
% 1.67/0.59  fof(f699,plain,(
% 1.67/0.59    $false | (spl5_8 | ~spl5_9)),
% 1.67/0.59    inference(subsumption_resolution,[],[f274,f277])).
% 1.67/0.59  fof(f277,plain,(
% 1.67/0.59    ( ! [X1] : (r2_hidden(sK0,X1)) ) | ~spl5_9),
% 1.67/0.59    inference(avatar_component_clause,[],[f276])).
% 1.67/0.59  fof(f276,plain,(
% 1.67/0.59    spl5_9 <=> ! [X1] : r2_hidden(sK0,X1)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.67/0.59  fof(f274,plain,(
% 1.67/0.59    ~r2_hidden(sK0,k1_tarski(sK1)) | spl5_8),
% 1.67/0.59    inference(avatar_component_clause,[],[f272])).
% 1.67/0.59  fof(f272,plain,(
% 1.67/0.59    spl5_8 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.67/0.59  fof(f697,plain,(
% 1.67/0.59    ~spl5_8),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f696])).
% 1.67/0.59  fof(f696,plain,(
% 1.67/0.59    $false | ~spl5_8),
% 1.67/0.59    inference(subsumption_resolution,[],[f691,f28])).
% 1.67/0.59  fof(f28,plain,(
% 1.67/0.59    sK0 != sK1),
% 1.67/0.59    inference(cnf_transformation,[],[f13])).
% 1.67/0.59  fof(f13,plain,(
% 1.67/0.59    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 1.67/0.59  fof(f12,plain,(
% 1.67/0.59    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1) => (k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1)),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f11,plain,(
% 1.67/0.59    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1)),
% 1.67/0.59    inference(ennf_transformation,[],[f10])).
% 1.67/0.59  fof(f10,negated_conjecture,(
% 1.67/0.59    ~! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.67/0.59    inference(negated_conjecture,[],[f9])).
% 1.67/0.59  fof(f9,conjecture,(
% 1.67/0.59    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 1.67/0.59  fof(f691,plain,(
% 1.67/0.59    sK0 = sK1 | ~spl5_8),
% 1.67/0.59    inference(resolution,[],[f273,f57])).
% 1.67/0.59  fof(f57,plain,(
% 1.67/0.59    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.67/0.59    inference(equality_resolution,[],[f42])).
% 1.67/0.59  fof(f42,plain,(
% 1.67/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f27,plain,(
% 1.67/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 1.67/0.59  fof(f26,plain,(
% 1.67/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f25,plain,(
% 1.67/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.67/0.59    inference(rectify,[],[f24])).
% 1.67/0.59  fof(f24,plain,(
% 1.67/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.67/0.59    inference(nnf_transformation,[],[f4])).
% 1.67/0.59  fof(f4,axiom,(
% 1.67/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.67/0.59  fof(f273,plain,(
% 1.67/0.59    r2_hidden(sK0,k1_tarski(sK1)) | ~spl5_8),
% 1.67/0.59    inference(avatar_component_clause,[],[f272])).
% 1.67/0.59  fof(f688,plain,(
% 1.67/0.59    ~spl5_5 | ~spl5_11),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f687])).
% 1.67/0.59  fof(f687,plain,(
% 1.67/0.59    $false | (~spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(subsumption_resolution,[],[f668,f28])).
% 1.67/0.59  fof(f668,plain,(
% 1.67/0.59    sK0 = sK1 | (~spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(resolution,[],[f664,f57])).
% 1.67/0.59  fof(f664,plain,(
% 1.67/0.59    r2_hidden(sK1,k1_tarski(sK0)) | (~spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(forward_demodulation,[],[f138,f370])).
% 1.67/0.59  fof(f370,plain,(
% 1.67/0.59    sK1 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) | ~spl5_11),
% 1.67/0.59    inference(avatar_component_clause,[],[f368])).
% 1.67/0.59  fof(f368,plain,(
% 1.67/0.59    spl5_11 <=> sK1 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.67/0.59  fof(f138,plain,(
% 1.67/0.59    r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0)) | ~spl5_5),
% 1.67/0.59    inference(avatar_component_clause,[],[f136])).
% 1.67/0.59  fof(f136,plain,(
% 1.67/0.59    spl5_5 <=> r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.67/0.59  fof(f658,plain,(
% 1.67/0.59    spl5_8 | ~spl5_10),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f657])).
% 1.67/0.59  fof(f657,plain,(
% 1.67/0.59    $false | (spl5_8 | ~spl5_10)),
% 1.67/0.59    inference(subsumption_resolution,[],[f656,f53])).
% 1.67/0.59  fof(f53,plain,(
% 1.67/0.59    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.67/0.59    inference(equality_resolution,[],[f52])).
% 1.67/0.59  fof(f52,plain,(
% 1.67/0.59    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.67/0.59    inference(equality_resolution,[],[f37])).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f23])).
% 1.67/0.59  fof(f23,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.67/0.59  fof(f22,plain,(
% 1.67/0.59    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f21,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.67/0.59    inference(rectify,[],[f20])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.67/0.59    inference(flattening,[],[f19])).
% 1.67/0.59  fof(f19,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.67/0.59    inference(nnf_transformation,[],[f5])).
% 1.67/0.59  fof(f5,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.67/0.59  fof(f656,plain,(
% 1.67/0.59    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (spl5_8 | ~spl5_10)),
% 1.67/0.59    inference(subsumption_resolution,[],[f655,f274])).
% 1.67/0.59  fof(f655,plain,(
% 1.67/0.59    r2_hidden(sK0,k1_tarski(sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_10),
% 1.67/0.59    inference(subsumption_resolution,[],[f654,f29])).
% 1.67/0.59  fof(f29,plain,(
% 1.67/0.59    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))),
% 1.67/0.59    inference(cnf_transformation,[],[f13])).
% 1.67/0.59  fof(f654,plain,(
% 1.67/0.59    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) | r2_hidden(sK0,k1_tarski(sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_10),
% 1.67/0.59    inference(subsumption_resolution,[],[f637,f56])).
% 1.67/0.59  fof(f56,plain,(
% 1.67/0.59    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.67/0.59    inference(equality_resolution,[],[f55])).
% 1.67/0.59  fof(f55,plain,(
% 1.67/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.67/0.59    inference(equality_resolution,[],[f43])).
% 1.67/0.59  fof(f43,plain,(
% 1.67/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f637,plain,(
% 1.67/0.59    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) | r2_hidden(sK0,k1_tarski(sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_10),
% 1.67/0.59    inference(superposition,[],[f35,f366])).
% 1.67/0.59  fof(f366,plain,(
% 1.67/0.59    sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) | ~spl5_10),
% 1.67/0.59    inference(avatar_component_clause,[],[f364])).
% 1.67/0.59  fof(f364,plain,(
% 1.67/0.59    spl5_10 <=> sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.67/0.59  fof(f35,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f18])).
% 1.67/0.59  fof(f18,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 1.67/0.59  fof(f17,plain,(
% 1.67/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f16,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.67/0.59    inference(rectify,[],[f15])).
% 1.67/0.59  fof(f15,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.67/0.59    inference(flattening,[],[f14])).
% 1.67/0.59  fof(f14,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.67/0.59    inference(nnf_transformation,[],[f1])).
% 1.67/0.59  fof(f1,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.67/0.59  fof(f614,plain,(
% 1.67/0.59    spl5_5 | ~spl5_11),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f613])).
% 1.67/0.59  fof(f613,plain,(
% 1.67/0.59    $false | (spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(subsumption_resolution,[],[f612,f56])).
% 1.67/0.59  fof(f612,plain,(
% 1.67/0.59    ~r2_hidden(sK1,k1_tarski(sK1)) | (spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(subsumption_resolution,[],[f611,f29])).
% 1.67/0.59  fof(f611,plain,(
% 1.67/0.59    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | (spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(subsumption_resolution,[],[f597,f592])).
% 1.67/0.59  fof(f592,plain,(
% 1.67/0.59    ~r2_hidden(sK1,k1_tarski(sK0)) | (spl5_5 | ~spl5_11)),
% 1.67/0.59    inference(superposition,[],[f137,f370])).
% 1.67/0.59  fof(f137,plain,(
% 1.67/0.59    ~r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0)) | spl5_5),
% 1.67/0.59    inference(avatar_component_clause,[],[f136])).
% 1.67/0.59  fof(f597,plain,(
% 1.67/0.59    r2_hidden(sK1,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | ~spl5_11),
% 1.67/0.59    inference(superposition,[],[f34,f370])).
% 1.67/0.59  fof(f34,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f18])).
% 1.67/0.59  fof(f371,plain,(
% 1.67/0.59    spl5_10 | spl5_11 | ~spl5_7),
% 1.67/0.59    inference(avatar_split_clause,[],[f353,f162,f368,f364])).
% 1.67/0.59  fof(f162,plain,(
% 1.67/0.59    spl5_7 <=> r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.67/0.59  fof(f353,plain,(
% 1.67/0.59    sK1 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) | ~spl5_7),
% 1.67/0.59    inference(resolution,[],[f164,f54])).
% 1.67/0.59  fof(f54,plain,(
% 1.67/0.59    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 1.67/0.59    inference(equality_resolution,[],[f36])).
% 1.67/0.59  fof(f36,plain,(
% 1.67/0.59    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f23])).
% 1.67/0.59  fof(f164,plain,(
% 1.67/0.59    r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1)) | ~spl5_7),
% 1.67/0.59    inference(avatar_component_clause,[],[f162])).
% 1.67/0.59  fof(f320,plain,(
% 1.67/0.59    spl5_9 | ~spl5_5 | spl5_7),
% 1.67/0.59    inference(avatar_split_clause,[],[f319,f162,f136,f276])).
% 1.67/0.59  fof(f319,plain,(
% 1.67/0.59    ( ! [X1] : (r2_hidden(sK0,X1)) ) | (~spl5_5 | spl5_7)),
% 1.67/0.59    inference(subsumption_resolution,[],[f310,f53])).
% 1.67/0.59  fof(f310,plain,(
% 1.67/0.59    ( ! [X1] : (r2_hidden(sK0,X1) | ~r2_hidden(sK0,k2_tarski(sK0,sK1))) ) | (~spl5_5 | spl5_7)),
% 1.67/0.59    inference(resolution,[],[f290,f47])).
% 1.67/0.59  fof(f47,plain,(
% 1.67/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.67/0.59    inference(equality_resolution,[],[f32])).
% 1.67/0.59  fof(f32,plain,(
% 1.67/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f18])).
% 1.67/0.59  fof(f290,plain,(
% 1.67/0.59    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),X0))) ) | (~spl5_5 | spl5_7)),
% 1.67/0.59    inference(forward_demodulation,[],[f281,f219])).
% 1.67/0.59  fof(f219,plain,(
% 1.67/0.59    sK0 = sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)) | ~spl5_5),
% 1.67/0.59    inference(resolution,[],[f138,f57])).
% 1.67/0.59  fof(f281,plain,(
% 1.67/0.59    ( ! [X0] : (~r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k2_tarski(sK0,sK1),X0))) ) | spl5_7),
% 1.67/0.59    inference(resolution,[],[f163,f49])).
% 1.67/0.59  fof(f49,plain,(
% 1.67/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.67/0.59    inference(equality_resolution,[],[f30])).
% 1.67/0.59  fof(f30,plain,(
% 1.67/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f18])).
% 1.67/0.59  fof(f163,plain,(
% 1.67/0.59    ~r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1)) | spl5_7),
% 1.67/0.59    inference(avatar_component_clause,[],[f162])).
% 1.67/0.59  fof(f165,plain,(
% 1.67/0.59    spl5_5 | spl5_7),
% 1.67/0.59    inference(avatar_split_clause,[],[f159,f162,f136])).
% 1.67/0.59  fof(f159,plain,(
% 1.67/0.59    r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k2_tarski(sK0,sK1)) | r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0))),
% 1.67/0.59    inference(equality_resolution,[],[f63])).
% 1.67/0.59  fof(f63,plain,(
% 1.67/0.59    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),X0),k2_tarski(sK0,sK1)) | r2_hidden(sK2(k2_tarski(sK0,sK1),k1_tarski(sK1),X0),X0)) )),
% 1.67/0.59    inference(superposition,[],[f29,f33])).
% 1.67/0.59  fof(f33,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f18])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (24563)------------------------------
% 1.67/0.59  % (24563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (24563)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.60  % (24563)Memory used [KB]: 11001
% 1.67/0.60  % (24563)Time elapsed: 0.180 s
% 1.67/0.60  % (24563)------------------------------
% 1.67/0.60  % (24563)------------------------------
% 1.67/0.60  % (24547)Success in time 0.23 s
%------------------------------------------------------------------------------
