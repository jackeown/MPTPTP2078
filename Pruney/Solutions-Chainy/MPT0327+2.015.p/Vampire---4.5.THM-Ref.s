%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:50 EST 2020

% Result     : Theorem 8.83s
% Output     : Refutation 8.83s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 255 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   21
%              Number of atoms          :  271 (1766 expanded)
%              Number of equality atoms :   99 ( 320 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12634,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f77,f110,f125,f12633])).

fof(f12633,plain,
    ( ~ spl4_2
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f12632])).

fof(f12632,plain,
    ( $false
    | ~ spl4_2
    | spl4_10 ),
    inference(subsumption_resolution,[],[f12610,f68])).

fof(f68,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f12610,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_10 ),
    inference(trivial_inequality_removal,[],[f12609])).

fof(f12609,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK1)
    | spl4_10 ),
    inference(superposition,[],[f123,f12342])).

fof(f12342,plain,(
    ! [X200,X201] :
      ( k2_xboole_0(X201,k1_tarski(X200)) = X201
      | ~ r2_hidden(X200,X201) ) ),
    inference(forward_demodulation,[],[f12162,f2454])).

fof(f2454,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X4)) = X3 ),
    inference(subsumption_resolution,[],[f2423,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f2423,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X3,k4_xboole_0(X4,X4)) = X3
      | ~ r1_tarski(X3,X3) ) ),
    inference(superposition,[],[f2105,f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2105,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(X36,X36)) = k2_xboole_0(X35,X35) ),
    inference(superposition,[],[f41,f2072])).

fof(f2072,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4) ),
    inference(subsumption_resolution,[],[f401,f510])).

fof(f510,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k4_xboole_0(X8,X8))
      | ~ r2_hidden(X10,X9) ) ),
    inference(superposition,[],[f53,f443])).

fof(f443,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f434])).

fof(f434,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1)
      | k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f165,f164])).

fof(f164,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK2(k4_xboole_0(X5,X6),X7,k4_xboole_0(X5,X6)),X5)
      | k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),X7) ) ),
    inference(resolution,[],[f154,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f165,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X8,X9),X10,k4_xboole_0(X8,X9)),X9)
      | k4_xboole_0(X8,X9) = k4_xboole_0(k4_xboole_0(X8,X9),X10) ) ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f401,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4)
      | r2_hidden(sK2(X4,X4,k4_xboole_0(X5,X5)),k4_xboole_0(X5,X5)) ) ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4)
      | k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4)
      | r2_hidden(sK2(X4,X4,k4_xboole_0(X5,X5)),k4_xboole_0(X5,X5)) ) ),
    inference(resolution,[],[f237,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1) ) ),
    inference(resolution,[],[f153,f152])).

fof(f152,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(sK2(X3,X4,k4_xboole_0(X5,X6)),X5)
      | k4_xboole_0(X3,X4) = k4_xboole_0(X5,X6)
      | r2_hidden(sK2(X3,X4,k4_xboole_0(X5,X6)),X3) ) ),
    inference(resolution,[],[f34,f54])).

fof(f153,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(sK2(X7,X8,k4_xboole_0(X9,X10)),X10)
      | k4_xboole_0(X9,X10) = k4_xboole_0(X7,X8)
      | r2_hidden(sK2(X7,X8,k4_xboole_0(X9,X10)),X7) ) ),
    inference(resolution,[],[f34,f53])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f12162,plain,(
    ! [X202,X200,X201] :
      ( k2_xboole_0(X201,k1_tarski(X200)) = k2_xboole_0(X201,k4_xboole_0(X202,X202))
      | ~ r2_hidden(X200,X201) ) ),
    inference(superposition,[],[f41,f2045])).

fof(f2045,plain,(
    ! [X39,X37,X38] :
      ( k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38)
      | ~ r2_hidden(X37,X38) ) ),
    inference(subsumption_resolution,[],[f2032,f510])).

fof(f2032,plain,(
    ! [X39,X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38)
      | r2_hidden(X37,k4_xboole_0(X39,X39)) ) ),
    inference(duplicate_literal_removal,[],[f2023])).

fof(f2023,plain,(
    ! [X39,X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38)
      | r2_hidden(X37,k4_xboole_0(X39,X39))
      | k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38) ) ),
    inference(superposition,[],[f35,f392])).

fof(f392,plain,(
    ! [X12,X13,X11] :
      ( sK2(k1_tarski(X11),X12,k4_xboole_0(X13,X13)) = X11
      | k4_xboole_0(X13,X13) = k4_xboole_0(k1_tarski(X11),X12) ) ),
    inference(resolution,[],[f237,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f123,plain,
    ( sK1 != k2_xboole_0(sK1,k1_tarski(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_10
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f125,plain,
    ( ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f113,f107,f121])).

fof(f107,plain,
    ( spl4_8
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( sK1 != k2_xboole_0(sK1,k1_tarski(sK0))
    | spl4_8 ),
    inference(superposition,[],[f109,f42])).

fof(f109,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f105,f73,f107])).

fof(f73,plain,
    ( spl4_3
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl4_3 ),
    inference(superposition,[],[f75,f41])).

fof(f75,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f77,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f71,f61,f73])).

fof(f61,plain,
    ( spl4_1
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_1 ),
    inference(superposition,[],[f63,f42])).

fof(f63,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f64,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.53  % (5543)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (5551)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (5559)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (5544)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (5545)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (5552)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (5560)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.56  % (5561)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (5551)Refutation not found, incomplete strategy% (5551)------------------------------
% 0.20/0.56  % (5551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5551)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5551)Memory used [KB]: 1663
% 0.20/0.56  % (5551)Time elapsed: 0.144 s
% 0.20/0.56  % (5551)------------------------------
% 0.20/0.56  % (5551)------------------------------
% 0.20/0.56  % (5553)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.57  % (5539)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.54/0.57  % (5563)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.54/0.57  % (5553)Refutation not found, incomplete strategy% (5553)------------------------------
% 1.54/0.57  % (5553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (5553)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (5553)Memory used [KB]: 10618
% 1.54/0.57  % (5553)Time elapsed: 0.146 s
% 1.54/0.57  % (5553)------------------------------
% 1.54/0.57  % (5553)------------------------------
% 1.54/0.57  % (5548)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.54/0.58  % (5556)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.58  % (5540)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.54/0.58  % (5557)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.58  % (5558)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.54/0.58  % (5555)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.54/0.58  % (5564)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.54/0.58  % (5565)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.54/0.58  % (5566)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.72/0.58  % (5541)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.72/0.58  % (5542)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.72/0.58  % (5547)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.72/0.59  % (5554)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.72/0.59  % (5554)Refutation not found, incomplete strategy% (5554)------------------------------
% 1.72/0.59  % (5554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (5554)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.59  
% 1.72/0.59  % (5554)Memory used [KB]: 1791
% 1.72/0.59  % (5554)Time elapsed: 0.138 s
% 1.72/0.59  % (5554)------------------------------
% 1.72/0.59  % (5554)------------------------------
% 1.72/0.59  % (5566)Refutation not found, incomplete strategy% (5566)------------------------------
% 1.72/0.59  % (5566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (5566)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.59  
% 1.72/0.59  % (5566)Memory used [KB]: 1663
% 1.72/0.59  % (5566)Time elapsed: 0.168 s
% 1.72/0.59  % (5566)------------------------------
% 1.72/0.59  % (5566)------------------------------
% 1.72/0.59  % (5538)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.72/0.59  % (5538)Refutation not found, incomplete strategy% (5538)------------------------------
% 1.72/0.59  % (5538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (5538)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.59  
% 1.72/0.59  % (5538)Memory used [KB]: 1663
% 1.72/0.59  % (5538)Time elapsed: 0.147 s
% 1.72/0.59  % (5538)------------------------------
% 1.72/0.59  % (5538)------------------------------
% 1.72/0.60  % (5546)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.72/0.60  % (5562)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.72/0.60  % (5550)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.72/0.60  % (5537)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.72/0.60  % (5549)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.07/0.67  % (5568)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.07/0.68  % (5540)Refutation not found, incomplete strategy% (5540)------------------------------
% 2.07/0.68  % (5540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.70  % (5540)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.70  
% 2.07/0.70  % (5540)Memory used [KB]: 6140
% 2.07/0.70  % (5540)Time elapsed: 0.258 s
% 2.07/0.70  % (5540)------------------------------
% 2.07/0.70  % (5540)------------------------------
% 2.07/0.71  % (5569)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.61/0.71  % (5570)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.61/0.72  % (5572)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.61/0.73  % (5575)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.61/0.76  % (5575)Refutation not found, incomplete strategy% (5575)------------------------------
% 2.61/0.76  % (5575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.61/0.76  % (5575)Termination reason: Refutation not found, incomplete strategy
% 2.61/0.76  
% 2.61/0.76  % (5575)Memory used [KB]: 10618
% 2.61/0.76  % (5575)Time elapsed: 0.114 s
% 2.61/0.76  % (5575)------------------------------
% 2.61/0.76  % (5575)------------------------------
% 2.98/0.85  % (5539)Time limit reached!
% 2.98/0.85  % (5539)------------------------------
% 2.98/0.85  % (5539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.85  % (5561)Time limit reached!
% 2.98/0.85  % (5561)------------------------------
% 2.98/0.85  % (5561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.85  % (5561)Termination reason: Time limit
% 2.98/0.85  
% 2.98/0.85  % (5561)Memory used [KB]: 13816
% 2.98/0.85  % (5561)Time elapsed: 0.421 s
% 2.98/0.85  % (5561)------------------------------
% 2.98/0.85  % (5561)------------------------------
% 3.43/0.86  % (5539)Termination reason: Time limit
% 3.43/0.86  % (5539)Termination phase: Saturation
% 3.43/0.86  
% 3.43/0.86  % (5539)Memory used [KB]: 7803
% 3.43/0.86  % (5539)Time elapsed: 0.424 s
% 3.43/0.86  % (5539)------------------------------
% 3.43/0.86  % (5539)------------------------------
% 3.43/0.86  % (5628)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.71/0.88  % (5661)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.71/0.92  % (5543)Time limit reached!
% 3.71/0.92  % (5543)------------------------------
% 3.71/0.92  % (5543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.92  % (5543)Termination reason: Time limit
% 3.71/0.92  
% 3.71/0.92  % (5543)Memory used [KB]: 15863
% 3.71/0.92  % (5543)Time elapsed: 0.504 s
% 3.71/0.92  % (5543)------------------------------
% 3.71/0.92  % (5543)------------------------------
% 4.07/0.99  % (5720)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.07/0.99  % (5718)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.51/1.03  % (5544)Time limit reached!
% 4.51/1.03  % (5544)------------------------------
% 4.51/1.03  % (5544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/1.05  % (5544)Termination reason: Time limit
% 4.51/1.05  % (5544)Termination phase: Saturation
% 4.51/1.05  
% 4.51/1.05  % (5544)Memory used [KB]: 6652
% 4.51/1.05  % (5544)Time elapsed: 0.600 s
% 4.51/1.05  % (5544)------------------------------
% 4.51/1.05  % (5544)------------------------------
% 4.51/1.05  % (5731)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.51/1.06  % (5731)Refutation not found, incomplete strategy% (5731)------------------------------
% 4.51/1.06  % (5731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/1.06  % (5731)Termination reason: Refutation not found, incomplete strategy
% 4.51/1.06  
% 4.51/1.06  % (5731)Memory used [KB]: 10746
% 4.51/1.06  % (5731)Time elapsed: 0.111 s
% 4.51/1.06  % (5731)------------------------------
% 4.51/1.06  % (5731)------------------------------
% 5.57/1.16  % (5784)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 6.28/1.18  % (5780)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 7.89/1.39  % (5661)Time limit reached!
% 7.89/1.39  % (5661)------------------------------
% 7.89/1.39  % (5661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.40  % (5661)Termination reason: Time limit
% 7.89/1.40  
% 7.89/1.40  % (5661)Memory used [KB]: 16375
% 7.89/1.40  % (5661)Time elapsed: 0.610 s
% 7.89/1.40  % (5661)------------------------------
% 7.89/1.40  % (5661)------------------------------
% 7.89/1.41  % (5570)Time limit reached!
% 7.89/1.41  % (5570)------------------------------
% 7.89/1.41  % (5570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.41  % (5570)Termination reason: Time limit
% 7.89/1.41  % (5570)Termination phase: Saturation
% 7.89/1.41  
% 7.89/1.41  % (5570)Memory used [KB]: 12409
% 7.89/1.41  % (5570)Time elapsed: 0.804 s
% 7.89/1.41  % (5570)------------------------------
% 7.89/1.41  % (5570)------------------------------
% 7.89/1.44  % (5549)Time limit reached!
% 7.89/1.44  % (5549)------------------------------
% 7.89/1.44  % (5549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.45  % (5549)Termination reason: Time limit
% 7.89/1.45  
% 7.89/1.45  % (5549)Memory used [KB]: 14328
% 7.89/1.45  % (5549)Time elapsed: 1.017 s
% 7.89/1.45  % (5549)------------------------------
% 7.89/1.45  % (5549)------------------------------
% 7.89/1.46  % (5564)Time limit reached!
% 7.89/1.46  % (5564)------------------------------
% 7.89/1.46  % (5564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.46  % (5564)Termination reason: Time limit
% 7.89/1.46  % (5564)Termination phase: Saturation
% 7.89/1.46  
% 7.89/1.46  % (5564)Memory used [KB]: 8699
% 7.89/1.46  % (5564)Time elapsed: 1.0000 s
% 7.89/1.46  % (5564)------------------------------
% 7.89/1.46  % (5564)------------------------------
% 8.83/1.49  % (5558)Refutation found. Thanks to Tanya!
% 8.83/1.49  % SZS status Theorem for theBenchmark
% 8.83/1.51  % SZS output start Proof for theBenchmark
% 8.83/1.51  fof(f12634,plain,(
% 8.83/1.51    $false),
% 8.83/1.51    inference(avatar_sat_refutation,[],[f64,f69,f77,f110,f125,f12633])).
% 8.83/1.51  fof(f12633,plain,(
% 8.83/1.51    ~spl4_2 | spl4_10),
% 8.83/1.51    inference(avatar_contradiction_clause,[],[f12632])).
% 8.83/1.51  fof(f12632,plain,(
% 8.83/1.51    $false | (~spl4_2 | spl4_10)),
% 8.83/1.51    inference(subsumption_resolution,[],[f12610,f68])).
% 8.83/1.51  fof(f68,plain,(
% 8.83/1.51    r2_hidden(sK0,sK1) | ~spl4_2),
% 8.83/1.51    inference(avatar_component_clause,[],[f66])).
% 8.83/1.51  fof(f66,plain,(
% 8.83/1.51    spl4_2 <=> r2_hidden(sK0,sK1)),
% 8.83/1.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 8.83/1.51  fof(f12610,plain,(
% 8.83/1.51    ~r2_hidden(sK0,sK1) | spl4_10),
% 8.83/1.51    inference(trivial_inequality_removal,[],[f12609])).
% 8.83/1.51  fof(f12609,plain,(
% 8.83/1.51    sK1 != sK1 | ~r2_hidden(sK0,sK1) | spl4_10),
% 8.83/1.51    inference(superposition,[],[f123,f12342])).
% 8.83/1.51  fof(f12342,plain,(
% 8.83/1.51    ( ! [X200,X201] : (k2_xboole_0(X201,k1_tarski(X200)) = X201 | ~r2_hidden(X200,X201)) )),
% 8.83/1.51    inference(forward_demodulation,[],[f12162,f2454])).
% 8.83/1.51  fof(f2454,plain,(
% 8.83/1.51    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X4)) = X3) )),
% 8.83/1.51    inference(subsumption_resolution,[],[f2423,f58])).
% 8.83/1.51  fof(f58,plain,(
% 8.83/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.83/1.51    inference(equality_resolution,[],[f48])).
% 8.83/1.51  fof(f48,plain,(
% 8.83/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.83/1.51    inference(cnf_transformation,[],[f28])).
% 8.83/1.51  fof(f28,plain,(
% 8.83/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.83/1.51    inference(flattening,[],[f27])).
% 8.83/1.51  fof(f27,plain,(
% 8.83/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.83/1.51    inference(nnf_transformation,[],[f3])).
% 8.83/1.51  fof(f3,axiom,(
% 8.83/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.83/1.51  fof(f2423,plain,(
% 8.83/1.51    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X4)) = X3 | ~r1_tarski(X3,X3)) )),
% 8.83/1.51    inference(superposition,[],[f2105,f79])).
% 8.83/1.51  fof(f79,plain,(
% 8.83/1.51    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 8.83/1.51    inference(superposition,[],[f43,f42])).
% 8.83/1.51  fof(f42,plain,(
% 8.83/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.83/1.51    inference(cnf_transformation,[],[f1])).
% 8.83/1.51  fof(f1,axiom,(
% 8.83/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 8.83/1.51  fof(f43,plain,(
% 8.83/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 8.83/1.51    inference(cnf_transformation,[],[f15])).
% 8.83/1.51  fof(f15,plain,(
% 8.83/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.83/1.51    inference(ennf_transformation,[],[f5])).
% 8.83/1.51  fof(f5,axiom,(
% 8.83/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 8.83/1.51  fof(f2105,plain,(
% 8.83/1.51    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(X36,X36)) = k2_xboole_0(X35,X35)) )),
% 8.83/1.51    inference(superposition,[],[f41,f2072])).
% 8.83/1.51  fof(f2072,plain,(
% 8.83/1.51    ( ! [X4,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4)) )),
% 8.83/1.51    inference(subsumption_resolution,[],[f401,f510])).
% 8.83/1.51  fof(f510,plain,(
% 8.83/1.51    ( ! [X10,X8,X9] : (~r2_hidden(X10,k4_xboole_0(X8,X8)) | ~r2_hidden(X10,X9)) )),
% 8.83/1.51    inference(superposition,[],[f53,f443])).
% 8.83/1.51  fof(f443,plain,(
% 8.83/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 8.83/1.51    inference(duplicate_literal_removal,[],[f434])).
% 8.83/1.51  fof(f434,plain,(
% 8.83/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) | k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 8.83/1.51    inference(resolution,[],[f165,f164])).
% 8.83/1.51  fof(f164,plain,(
% 8.83/1.51    ( ! [X6,X7,X5] : (r2_hidden(sK2(k4_xboole_0(X5,X6),X7,k4_xboole_0(X5,X6)),X5) | k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),X7)) )),
% 8.83/1.51    inference(resolution,[],[f154,f54])).
% 8.83/1.51  fof(f54,plain,(
% 8.83/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 8.83/1.51    inference(equality_resolution,[],[f31])).
% 8.83/1.51  fof(f31,plain,(
% 8.83/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 8.83/1.51    inference(cnf_transformation,[],[f22])).
% 8.83/1.51  fof(f22,plain,(
% 8.83/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.83/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 8.83/1.51  fof(f21,plain,(
% 8.83/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 8.83/1.51    introduced(choice_axiom,[])).
% 8.83/1.51  fof(f20,plain,(
% 8.83/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.83/1.51    inference(rectify,[],[f19])).
% 8.83/1.51  fof(f19,plain,(
% 8.83/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.83/1.51    inference(flattening,[],[f18])).
% 8.83/1.51  fof(f18,plain,(
% 8.83/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.83/1.51    inference(nnf_transformation,[],[f2])).
% 8.83/1.51  fof(f2,axiom,(
% 8.83/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 8.83/1.51  fof(f154,plain,(
% 8.83/1.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 8.83/1.51    inference(factoring,[],[f34])).
% 8.83/1.51  fof(f34,plain,(
% 8.83/1.51    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 8.83/1.51    inference(cnf_transformation,[],[f22])).
% 8.83/1.51  fof(f165,plain,(
% 8.83/1.51    ( ! [X10,X8,X9] : (~r2_hidden(sK2(k4_xboole_0(X8,X9),X10,k4_xboole_0(X8,X9)),X9) | k4_xboole_0(X8,X9) = k4_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 8.83/1.51    inference(resolution,[],[f154,f53])).
% 8.83/1.51  fof(f53,plain,(
% 8.83/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 8.83/1.51    inference(equality_resolution,[],[f32])).
% 8.83/1.51  fof(f32,plain,(
% 8.83/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 8.83/1.51    inference(cnf_transformation,[],[f22])).
% 8.83/1.51  fof(f401,plain,(
% 8.83/1.51    ( ! [X4,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4) | r2_hidden(sK2(X4,X4,k4_xboole_0(X5,X5)),k4_xboole_0(X5,X5))) )),
% 8.83/1.51    inference(duplicate_literal_removal,[],[f389])).
% 8.83/1.51  fof(f389,plain,(
% 8.83/1.51    ( ! [X4,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4) | k4_xboole_0(X5,X5) = k4_xboole_0(X4,X4) | r2_hidden(sK2(X4,X4,k4_xboole_0(X5,X5)),k4_xboole_0(X5,X5))) )),
% 8.83/1.51    inference(resolution,[],[f237,f35])).
% 8.83/1.51  fof(f35,plain,(
% 8.83/1.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 8.83/1.51    inference(cnf_transformation,[],[f22])).
% 8.83/1.51  fof(f237,plain,(
% 8.83/1.51    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)) )),
% 8.83/1.51    inference(duplicate_literal_removal,[],[f232])).
% 8.83/1.51  fof(f232,plain,(
% 8.83/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1)) )),
% 8.83/1.51    inference(resolution,[],[f153,f152])).
% 8.83/1.51  fof(f152,plain,(
% 8.83/1.51    ( ! [X6,X4,X5,X3] : (r2_hidden(sK2(X3,X4,k4_xboole_0(X5,X6)),X5) | k4_xboole_0(X3,X4) = k4_xboole_0(X5,X6) | r2_hidden(sK2(X3,X4,k4_xboole_0(X5,X6)),X3)) )),
% 8.83/1.51    inference(resolution,[],[f34,f54])).
% 8.83/1.51  fof(f153,plain,(
% 8.83/1.51    ( ! [X10,X8,X7,X9] : (~r2_hidden(sK2(X7,X8,k4_xboole_0(X9,X10)),X10) | k4_xboole_0(X9,X10) = k4_xboole_0(X7,X8) | r2_hidden(sK2(X7,X8,k4_xboole_0(X9,X10)),X7)) )),
% 8.83/1.51    inference(resolution,[],[f34,f53])).
% 8.83/1.51  fof(f41,plain,(
% 8.83/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.83/1.51    inference(cnf_transformation,[],[f6])).
% 8.83/1.51  fof(f6,axiom,(
% 8.83/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 8.83/1.51  fof(f12162,plain,(
% 8.83/1.51    ( ! [X202,X200,X201] : (k2_xboole_0(X201,k1_tarski(X200)) = k2_xboole_0(X201,k4_xboole_0(X202,X202)) | ~r2_hidden(X200,X201)) )),
% 8.83/1.51    inference(superposition,[],[f41,f2045])).
% 8.83/1.51  fof(f2045,plain,(
% 8.83/1.51    ( ! [X39,X37,X38] : (k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38) | ~r2_hidden(X37,X38)) )),
% 8.83/1.51    inference(subsumption_resolution,[],[f2032,f510])).
% 8.83/1.51  fof(f2032,plain,(
% 8.83/1.51    ( ! [X39,X37,X38] : (~r2_hidden(X37,X38) | k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38) | r2_hidden(X37,k4_xboole_0(X39,X39))) )),
% 8.83/1.51    inference(duplicate_literal_removal,[],[f2023])).
% 8.83/1.51  fof(f2023,plain,(
% 8.83/1.51    ( ! [X39,X37,X38] : (~r2_hidden(X37,X38) | k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38) | r2_hidden(X37,k4_xboole_0(X39,X39)) | k4_xboole_0(X39,X39) = k4_xboole_0(k1_tarski(X37),X38)) )),
% 8.83/1.51    inference(superposition,[],[f35,f392])).
% 8.83/1.51  fof(f392,plain,(
% 8.83/1.51    ( ! [X12,X13,X11] : (sK2(k1_tarski(X11),X12,k4_xboole_0(X13,X13)) = X11 | k4_xboole_0(X13,X13) = k4_xboole_0(k1_tarski(X11),X12)) )),
% 8.83/1.51    inference(resolution,[],[f237,f57])).
% 8.83/1.51  fof(f57,plain,(
% 8.83/1.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 8.83/1.51    inference(equality_resolution,[],[f37])).
% 8.83/1.51  fof(f37,plain,(
% 8.83/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 8.83/1.51    inference(cnf_transformation,[],[f26])).
% 8.83/1.51  fof(f26,plain,(
% 8.83/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 8.83/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 8.83/1.51  fof(f25,plain,(
% 8.83/1.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 8.83/1.51    introduced(choice_axiom,[])).
% 8.83/1.51  fof(f24,plain,(
% 8.83/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 8.83/1.51    inference(rectify,[],[f23])).
% 8.83/1.51  fof(f23,plain,(
% 8.83/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 8.83/1.51    inference(nnf_transformation,[],[f8])).
% 8.83/1.51  fof(f8,axiom,(
% 8.83/1.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 8.83/1.51  fof(f123,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) | spl4_10),
% 8.83/1.51    inference(avatar_component_clause,[],[f121])).
% 8.83/1.51  fof(f121,plain,(
% 8.83/1.51    spl4_10 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 8.83/1.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 8.83/1.51  fof(f125,plain,(
% 8.83/1.51    ~spl4_10 | spl4_8),
% 8.83/1.51    inference(avatar_split_clause,[],[f113,f107,f121])).
% 8.83/1.51  fof(f107,plain,(
% 8.83/1.51    spl4_8 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 8.83/1.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 8.83/1.51  fof(f113,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) | spl4_8),
% 8.83/1.51    inference(superposition,[],[f109,f42])).
% 8.83/1.51  fof(f109,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl4_8),
% 8.83/1.51    inference(avatar_component_clause,[],[f107])).
% 8.83/1.51  fof(f110,plain,(
% 8.83/1.51    ~spl4_8 | spl4_3),
% 8.83/1.51    inference(avatar_split_clause,[],[f105,f73,f107])).
% 8.83/1.51  fof(f73,plain,(
% 8.83/1.51    spl4_3 <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 8.83/1.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 8.83/1.51  fof(f105,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl4_3),
% 8.83/1.51    inference(superposition,[],[f75,f41])).
% 8.83/1.51  fof(f75,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl4_3),
% 8.83/1.51    inference(avatar_component_clause,[],[f73])).
% 8.83/1.51  fof(f77,plain,(
% 8.83/1.51    ~spl4_3 | spl4_1),
% 8.83/1.51    inference(avatar_split_clause,[],[f71,f61,f73])).
% 8.83/1.51  fof(f61,plain,(
% 8.83/1.51    spl4_1 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 8.83/1.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 8.83/1.51  fof(f71,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl4_1),
% 8.83/1.51    inference(superposition,[],[f63,f42])).
% 8.83/1.51  fof(f63,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_1),
% 8.83/1.51    inference(avatar_component_clause,[],[f61])).
% 8.83/1.51  fof(f69,plain,(
% 8.83/1.51    spl4_2),
% 8.83/1.51    inference(avatar_split_clause,[],[f29,f66])).
% 8.83/1.51  fof(f29,plain,(
% 8.83/1.51    r2_hidden(sK0,sK1)),
% 8.83/1.51    inference(cnf_transformation,[],[f17])).
% 8.83/1.51  fof(f17,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 8.83/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 8.83/1.51  fof(f16,plain,(
% 8.83/1.51    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 8.83/1.51    introduced(choice_axiom,[])).
% 8.83/1.51  fof(f14,plain,(
% 8.83/1.51    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 8.83/1.51    inference(ennf_transformation,[],[f13])).
% 8.83/1.51  fof(f13,negated_conjecture,(
% 8.83/1.51    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 8.83/1.51    inference(negated_conjecture,[],[f12])).
% 8.83/1.51  fof(f12,conjecture,(
% 8.83/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 8.83/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 8.83/1.51  fof(f64,plain,(
% 8.83/1.51    ~spl4_1),
% 8.83/1.51    inference(avatar_split_clause,[],[f30,f61])).
% 8.83/1.51  fof(f30,plain,(
% 8.83/1.51    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 8.83/1.51    inference(cnf_transformation,[],[f17])).
% 8.83/1.51  % SZS output end Proof for theBenchmark
% 8.83/1.51  % (5558)------------------------------
% 8.83/1.51  % (5558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.83/1.51  % (5558)Termination reason: Refutation
% 8.83/1.51  
% 8.83/1.51  % (5558)Memory used [KB]: 15991
% 8.83/1.51  % (5558)Time elapsed: 1.077 s
% 8.83/1.51  % (5558)------------------------------
% 8.83/1.51  % (5558)------------------------------
% 8.83/1.52  % (5536)Success in time 1.162 s
%------------------------------------------------------------------------------
