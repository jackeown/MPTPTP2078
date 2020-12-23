%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:02 EST 2020

% Result     : Theorem 11.57s
% Output     : Refutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 291 expanded)
%              Number of leaves         :   16 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  285 (1039 expanded)
%              Number of equality atoms :   71 ( 337 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f256,f337,f1160,f1162,f6210,f6247,f7343])).

fof(f7343,plain,(
    ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f7342])).

fof(f7342,plain,
    ( $false
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f6219,f5622])).

fof(f5622,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f595,f594])).

fof(f594,plain,(
    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f97,f66])).

fof(f66,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f97,plain,(
    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f72,plain,(
    ~ r1_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f595,plain,(
    ! [X0] : ~ r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f97,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f6219,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f6217])).

fof(f6217,plain,
    ( spl6_23
  <=> r2_hidden(sK0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f6247,plain,
    ( spl6_23
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f6246,f334,f249,f6217])).

fof(f249,plain,
    ( spl6_1
  <=> r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f334,plain,
    ( spl6_3
  <=> r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f6246,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f335,f1362])).

fof(f1362,plain,
    ( sK0 = sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f251,f66])).

fof(f251,plain,
    ( r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f249])).

fof(f335,plain,
    ( r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f334])).

fof(f6210,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f6209])).

fof(f6209,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f32,f6197])).

fof(f6197,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_1
    | spl6_2 ),
    inference(superposition,[],[f254,f1362])).

fof(f254,plain,
    ( ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl6_2
  <=> r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1162,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f463,f334,f253,f249])).

fof(f463,plain,
    ( r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != X2
      | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
      | ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2),sK1)
      | ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2),X2) ) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f33,f55,f37,f55])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f1160,plain,
    ( spl6_3
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f1153,f253,f249,f334])).

fof(f1153,plain,
    ( r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f255,f250,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f250,plain,
    ( ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f249])).

fof(f255,plain,
    ( r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f253])).

fof(f337,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f331,f334,f249])).

fof(f331,plain,
    ( ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X1] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != X1
      | ~ r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
      | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1),X1) ) ),
    inference(superposition,[],[f56,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f256,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f246,f253,f249])).

fof(f246,plain,
    ( r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
      | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0),sK1)
      | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0),X0) ) ),
    inference(superposition,[],[f56,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (27154)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (27171)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (27148)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (27162)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (27156)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (27160)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (27171)Refutation not found, incomplete strategy% (27171)------------------------------
% 0.21/0.52  % (27171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27171)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27171)Memory used [KB]: 1663
% 0.21/0.52  % (27171)Time elapsed: 0.113 s
% 0.21/0.52  % (27171)------------------------------
% 0.21/0.52  % (27171)------------------------------
% 0.21/0.52  % (27141)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (27145)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (27155)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (27147)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (27143)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (27142)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (27150)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (27161)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (27146)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (27149)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (27152)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (27168)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27153)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (27164)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (27151)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (27144)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (27167)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (27155)Refutation not found, incomplete strategy% (27155)------------------------------
% 0.21/0.55  % (27155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27166)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (27155)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27155)Memory used [KB]: 1663
% 0.21/0.55  % (27155)Time elapsed: 0.109 s
% 0.21/0.55  % (27155)------------------------------
% 0.21/0.55  % (27155)------------------------------
% 0.21/0.55  % (27170)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (27159)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (27169)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (27157)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (27142)Refutation not found, incomplete strategy% (27142)------------------------------
% 0.21/0.56  % (27142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27142)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27142)Memory used [KB]: 1663
% 0.21/0.56  % (27142)Time elapsed: 0.153 s
% 0.21/0.56  % (27142)------------------------------
% 0.21/0.56  % (27142)------------------------------
% 0.21/0.56  % (27158)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (27165)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (27157)Refutation not found, incomplete strategy% (27157)------------------------------
% 0.21/0.56  % (27157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27157)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27157)Memory used [KB]: 10618
% 0.21/0.57  % (27157)Time elapsed: 0.159 s
% 0.21/0.57  % (27157)------------------------------
% 0.21/0.57  % (27157)------------------------------
% 0.21/0.57  % (27151)Refutation not found, incomplete strategy% (27151)------------------------------
% 0.21/0.57  % (27151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27158)Refutation not found, incomplete strategy% (27158)------------------------------
% 0.21/0.57  % (27158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27158)Memory used [KB]: 1663
% 0.21/0.57  % (27158)Time elapsed: 0.168 s
% 0.21/0.57  % (27158)------------------------------
% 0.21/0.57  % (27158)------------------------------
% 0.21/0.58  % (27151)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (27151)Memory used [KB]: 10746
% 0.21/0.58  % (27151)Time elapsed: 0.170 s
% 0.21/0.58  % (27151)------------------------------
% 0.21/0.58  % (27151)------------------------------
% 0.21/0.58  % (27170)Refutation not found, incomplete strategy% (27170)------------------------------
% 0.21/0.58  % (27170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (27170)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (27170)Memory used [KB]: 10746
% 0.21/0.58  % (27170)Time elapsed: 0.178 s
% 0.21/0.58  % (27170)------------------------------
% 0.21/0.58  % (27170)------------------------------
% 2.11/0.66  % (27141)Refutation not found, incomplete strategy% (27141)------------------------------
% 2.11/0.66  % (27141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (27141)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.68  
% 2.11/0.68  % (27141)Memory used [KB]: 1791
% 2.11/0.68  % (27141)Time elapsed: 0.245 s
% 2.11/0.68  % (27141)------------------------------
% 2.11/0.68  % (27141)------------------------------
% 2.11/0.68  % (27144)Refutation not found, incomplete strategy% (27144)------------------------------
% 2.11/0.68  % (27144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (27144)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.68  
% 2.11/0.68  % (27144)Memory used [KB]: 6140
% 2.11/0.68  % (27144)Time elapsed: 0.273 s
% 2.11/0.68  % (27144)------------------------------
% 2.11/0.68  % (27144)------------------------------
% 2.11/0.68  % (27153)Refutation not found, incomplete strategy% (27153)------------------------------
% 2.11/0.68  % (27153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.69  % (27174)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.11/0.69  % (27172)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.11/0.69  % (27173)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.11/0.70  % (27153)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.70  
% 2.11/0.70  % (27153)Memory used [KB]: 10874
% 2.11/0.70  % (27153)Time elapsed: 0.270 s
% 2.11/0.70  % (27153)------------------------------
% 2.11/0.70  % (27153)------------------------------
% 2.11/0.71  % (27175)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.11/0.71  % (27174)Refutation not found, incomplete strategy% (27174)------------------------------
% 2.11/0.71  % (27174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.71  % (27174)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.71  
% 2.11/0.71  % (27174)Memory used [KB]: 6268
% 2.11/0.71  % (27174)Time elapsed: 0.127 s
% 2.11/0.71  % (27174)------------------------------
% 2.11/0.71  % (27174)------------------------------
% 2.11/0.72  % (27176)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.85/0.72  % (27177)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.85/0.72  % (27178)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.85/0.73  % (27176)Refutation not found, incomplete strategy% (27176)------------------------------
% 2.85/0.73  % (27176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.74  % (27176)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.74  
% 2.85/0.74  % (27176)Memory used [KB]: 10618
% 2.85/0.74  % (27176)Time elapsed: 0.133 s
% 2.85/0.74  % (27176)------------------------------
% 2.85/0.74  % (27176)------------------------------
% 3.36/0.81  % (27179)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.36/0.81  % (27166)Time limit reached!
% 3.36/0.81  % (27166)------------------------------
% 3.36/0.81  % (27166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.81  % (27166)Termination reason: Time limit
% 3.36/0.81  
% 3.36/0.81  % (27166)Memory used [KB]: 12920
% 3.36/0.81  % (27166)Time elapsed: 0.407 s
% 3.36/0.81  % (27166)------------------------------
% 3.36/0.81  % (27166)------------------------------
% 3.36/0.81  % (27143)Time limit reached!
% 3.36/0.81  % (27143)------------------------------
% 3.36/0.81  % (27143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.81  % (27143)Termination reason: Time limit
% 3.36/0.81  
% 3.36/0.81  % (27143)Memory used [KB]: 6524
% 3.36/0.81  % (27143)Time elapsed: 0.406 s
% 3.36/0.81  % (27143)------------------------------
% 3.36/0.81  % (27143)------------------------------
% 3.36/0.83  % (27180)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.36/0.84  % (27181)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.36/0.84  % (27182)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.36/0.84  % (27156)Refutation not found, incomplete strategy% (27156)------------------------------
% 3.36/0.84  % (27156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.85  % (27156)Termination reason: Refutation not found, incomplete strategy
% 3.36/0.85  
% 3.36/0.85  % (27156)Memory used [KB]: 6524
% 3.36/0.85  % (27156)Time elapsed: 0.440 s
% 3.36/0.85  % (27156)------------------------------
% 3.36/0.85  % (27156)------------------------------
% 3.36/0.86  % (27181)Refutation not found, incomplete strategy% (27181)------------------------------
% 3.36/0.86  % (27181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.86  % (27181)Termination reason: Refutation not found, incomplete strategy
% 3.36/0.86  
% 3.36/0.86  % (27181)Memory used [KB]: 10746
% 3.36/0.86  % (27181)Time elapsed: 0.131 s
% 3.36/0.86  % (27181)------------------------------
% 3.36/0.86  % (27181)------------------------------
% 3.94/0.88  % (27183)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.21/0.94  % (27147)Time limit reached!
% 4.21/0.94  % (27147)------------------------------
% 4.21/0.94  % (27147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.94  % (27147)Termination reason: Time limit
% 4.21/0.94  
% 4.21/0.94  % (27147)Memory used [KB]: 15095
% 4.21/0.94  % (27147)Time elapsed: 0.504 s
% 4.21/0.94  % (27147)------------------------------
% 4.21/0.94  % (27147)------------------------------
% 4.21/0.96  % (27185)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 4.21/0.98  % (27186)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 4.21/0.99  % (27184)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.21/1.00  % (27187)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 4.21/1.01  % (27148)Time limit reached!
% 4.21/1.01  % (27148)------------------------------
% 4.21/1.01  % (27148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/1.01  % (27148)Termination reason: Time limit
% 4.21/1.01  % (27148)Termination phase: Saturation
% 4.21/1.01  
% 4.21/1.01  % (27148)Memory used [KB]: 4989
% 4.21/1.01  % (27148)Time elapsed: 0.600 s
% 4.21/1.01  % (27148)------------------------------
% 4.21/1.01  % (27148)------------------------------
% 4.71/1.07  % (27186)Refutation not found, incomplete strategy% (27186)------------------------------
% 4.71/1.07  % (27186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.07  % (27188)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 4.71/1.07  % (27186)Termination reason: Refutation not found, incomplete strategy
% 4.71/1.07  
% 4.71/1.07  % (27186)Memory used [KB]: 6268
% 4.71/1.07  % (27186)Time elapsed: 0.183 s
% 4.71/1.07  % (27186)------------------------------
% 4.71/1.07  % (27186)------------------------------
% 5.17/1.14  % (27187)Refutation not found, incomplete strategy% (27187)------------------------------
% 5.17/1.14  % (27187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.17/1.14  % (27187)Termination reason: Refutation not found, incomplete strategy
% 5.17/1.14  
% 5.17/1.14  % (27187)Memory used [KB]: 6140
% 5.17/1.14  % (27187)Time elapsed: 0.260 s
% 5.17/1.14  % (27187)------------------------------
% 5.17/1.14  % (27187)------------------------------
% 5.17/1.15  % (27189)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 6.52/1.19  % (27190)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 6.82/1.23  % (27185)Time limit reached!
% 6.82/1.23  % (27185)------------------------------
% 6.82/1.23  % (27185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.23  % (27185)Termination reason: Time limit
% 6.82/1.23  % (27185)Termination phase: Saturation
% 6.82/1.23  
% 6.82/1.23  % (27185)Memory used [KB]: 12920
% 6.82/1.23  % (27185)Time elapsed: 0.400 s
% 6.82/1.23  % (27185)------------------------------
% 6.82/1.23  % (27185)------------------------------
% 6.82/1.23  % (27178)Time limit reached!
% 6.82/1.23  % (27178)------------------------------
% 6.82/1.23  % (27178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.23  % (27178)Termination reason: Time limit
% 6.82/1.23  
% 6.82/1.23  % (27178)Memory used [KB]: 15863
% 6.82/1.23  % (27178)Time elapsed: 0.630 s
% 6.82/1.23  % (27178)------------------------------
% 6.82/1.23  % (27178)------------------------------
% 6.82/1.27  % (27191)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 7.50/1.36  % (27192)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 8.04/1.41  % (27169)Time limit reached!
% 8.04/1.41  % (27169)------------------------------
% 8.04/1.41  % (27169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.41  % (27169)Termination reason: Time limit
% 8.04/1.41  % (27169)Termination phase: Saturation
% 8.04/1.41  
% 8.04/1.41  % (27169)Memory used [KB]: 11257
% 8.04/1.41  % (27169)Time elapsed: 1.0000 s
% 8.04/1.41  % (27169)------------------------------
% 8.04/1.41  % (27169)------------------------------
% 8.04/1.45  % (27189)Time limit reached!
% 8.04/1.45  % (27189)------------------------------
% 8.04/1.45  % (27189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.45  % (27189)Termination reason: Time limit
% 8.04/1.45  
% 8.04/1.45  % (27189)Memory used [KB]: 8571
% 8.04/1.45  % (27189)Time elapsed: 0.413 s
% 8.04/1.45  % (27189)------------------------------
% 8.04/1.45  % (27189)------------------------------
% 8.04/1.47  % (27188)Time limit reached!
% 8.04/1.47  % (27188)------------------------------
% 8.04/1.47  % (27188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.47  % (27188)Termination reason: Time limit
% 8.04/1.47  
% 8.04/1.47  % (27188)Memory used [KB]: 10874
% 8.04/1.47  % (27188)Time elapsed: 0.513 s
% 8.04/1.47  % (27188)------------------------------
% 8.04/1.47  % (27188)------------------------------
% 9.14/1.55  % (27191)Time limit reached!
% 9.14/1.55  % (27191)------------------------------
% 9.14/1.55  % (27191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.14/1.55  % (27191)Termination reason: Time limit
% 9.14/1.55  
% 9.14/1.55  % (27191)Memory used [KB]: 3198
% 9.14/1.55  % (27191)Time elapsed: 0.405 s
% 9.14/1.55  % (27191)------------------------------
% 9.14/1.55  % (27191)------------------------------
% 9.78/1.68  % (27192)Time limit reached!
% 9.78/1.68  % (27192)------------------------------
% 9.78/1.68  % (27192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.70  % (27192)Termination reason: Time limit
% 10.54/1.70  % (27192)Termination phase: Saturation
% 10.54/1.70  
% 10.54/1.70  % (27192)Memory used [KB]: 9083
% 10.54/1.70  % (27192)Time elapsed: 0.400 s
% 10.54/1.70  % (27192)------------------------------
% 10.54/1.70  % (27192)------------------------------
% 10.54/1.73  % (27146)Time limit reached!
% 10.54/1.73  % (27146)------------------------------
% 10.54/1.73  % (27146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.73  % (27146)Termination reason: Time limit
% 10.54/1.73  
% 10.54/1.73  % (27146)Memory used [KB]: 9850
% 10.54/1.73  % (27146)Time elapsed: 1.326 s
% 10.54/1.73  % (27146)------------------------------
% 10.54/1.73  % (27146)------------------------------
% 11.57/1.85  % (27183)Refutation found. Thanks to Tanya!
% 11.57/1.85  % SZS status Theorem for theBenchmark
% 11.57/1.85  % SZS output start Proof for theBenchmark
% 11.57/1.85  fof(f7344,plain,(
% 11.57/1.85    $false),
% 11.57/1.85    inference(avatar_sat_refutation,[],[f256,f337,f1160,f1162,f6210,f6247,f7343])).
% 11.57/1.85  fof(f7343,plain,(
% 11.57/1.85    ~spl6_23),
% 11.57/1.85    inference(avatar_contradiction_clause,[],[f7342])).
% 11.57/1.85  fof(f7342,plain,(
% 11.57/1.85    $false | ~spl6_23),
% 11.57/1.85    inference(subsumption_resolution,[],[f6219,f5622])).
% 11.57/1.85  fof(f5622,plain,(
% 11.57/1.85    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0)))) )),
% 11.57/1.85    inference(superposition,[],[f595,f594])).
% 11.57/1.85  fof(f594,plain,(
% 11.57/1.85    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.85    inference(unit_resulting_resolution,[],[f97,f66])).
% 11.57/1.85  fof(f66,plain,(
% 11.57/1.85    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.57/1.85    inference(equality_resolution,[],[f63])).
% 11.57/1.85  fof(f63,plain,(
% 11.57/1.85    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.57/1.85    inference(definition_unfolding,[],[f43,f55])).
% 11.57/1.85  fof(f55,plain,(
% 11.57/1.85    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.57/1.85    inference(definition_unfolding,[],[f34,f54])).
% 11.57/1.85  fof(f54,plain,(
% 11.57/1.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.57/1.85    inference(definition_unfolding,[],[f36,f47])).
% 11.57/1.85  fof(f47,plain,(
% 11.57/1.85    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.57/1.85    inference(cnf_transformation,[],[f9])).
% 11.57/1.85  fof(f9,axiom,(
% 11.57/1.85    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 11.57/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 11.57/1.85  fof(f36,plain,(
% 11.57/1.85    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.57/1.85    inference(cnf_transformation,[],[f8])).
% 11.57/1.85  fof(f8,axiom,(
% 11.57/1.85    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.57/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 11.57/1.85  fof(f34,plain,(
% 11.57/1.85    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.57/1.85    inference(cnf_transformation,[],[f7])).
% 11.57/1.85  fof(f7,axiom,(
% 11.57/1.85    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.57/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 11.57/1.85  fof(f43,plain,(
% 11.57/1.85    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.57/1.85    inference(cnf_transformation,[],[f26])).
% 11.57/1.85  fof(f26,plain,(
% 11.57/1.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.57/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 11.57/1.85  fof(f25,plain,(
% 11.57/1.85    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 11.57/1.85    introduced(choice_axiom,[])).
% 11.57/1.85  fof(f24,plain,(
% 11.57/1.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.57/1.85    inference(rectify,[],[f23])).
% 11.57/1.85  fof(f23,plain,(
% 11.57/1.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.57/1.85    inference(nnf_transformation,[],[f6])).
% 11.57/1.85  fof(f6,axiom,(
% 11.57/1.85    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.57/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 11.57/1.85  fof(f97,plain,(
% 11.57/1.85    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.85    inference(unit_resulting_resolution,[],[f72,f41])).
% 11.57/1.85  fof(f41,plain,(
% 11.57/1.85    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.57/1.85    inference(cnf_transformation,[],[f22])).
% 11.57/1.86  fof(f22,plain,(
% 11.57/1.86    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.57/1.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f21])).
% 11.57/1.86  fof(f21,plain,(
% 11.57/1.86    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 11.57/1.86    introduced(choice_axiom,[])).
% 11.57/1.86  fof(f16,plain,(
% 11.57/1.86    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.57/1.86    inference(ennf_transformation,[],[f13])).
% 11.57/1.86  fof(f13,plain,(
% 11.57/1.86    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.57/1.86    inference(rectify,[],[f3])).
% 11.57/1.86  fof(f3,axiom,(
% 11.57/1.86    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.57/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 11.57/1.86  fof(f72,plain,(
% 11.57/1.86    ~r1_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.86    inference(unit_resulting_resolution,[],[f65,f32,f42])).
% 11.57/1.86  fof(f42,plain,(
% 11.57/1.86    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.57/1.86    inference(cnf_transformation,[],[f22])).
% 11.57/1.86  fof(f32,plain,(
% 11.57/1.86    r2_hidden(sK0,sK1)),
% 11.57/1.86    inference(cnf_transformation,[],[f18])).
% 11.57/1.86  fof(f18,plain,(
% 11.57/1.86    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 11.57/1.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f17])).
% 11.57/1.86  fof(f17,plain,(
% 11.57/1.86    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 11.57/1.86    introduced(choice_axiom,[])).
% 11.57/1.86  fof(f14,plain,(
% 11.57/1.86    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 11.57/1.86    inference(ennf_transformation,[],[f11])).
% 11.57/1.86  fof(f11,negated_conjecture,(
% 11.57/1.86    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 11.57/1.86    inference(negated_conjecture,[],[f10])).
% 11.57/1.86  fof(f10,conjecture,(
% 11.57/1.86    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 11.57/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 11.57/1.86  fof(f65,plain,(
% 11.57/1.86    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 11.57/1.86    inference(equality_resolution,[],[f64])).
% 11.57/1.86  fof(f64,plain,(
% 11.57/1.86    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 11.57/1.86    inference(equality_resolution,[],[f62])).
% 11.57/1.86  fof(f62,plain,(
% 11.57/1.86    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.57/1.86    inference(definition_unfolding,[],[f44,f55])).
% 11.57/1.86  fof(f44,plain,(
% 11.57/1.86    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.57/1.86    inference(cnf_transformation,[],[f26])).
% 11.57/1.86  fof(f595,plain,(
% 11.57/1.86    ( ! [X0] : (~r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0)))) )),
% 11.57/1.86    inference(unit_resulting_resolution,[],[f97,f68])).
% 11.57/1.86  fof(f68,plain,(
% 11.57/1.86    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.57/1.86    inference(equality_resolution,[],[f49])).
% 11.57/1.86  fof(f49,plain,(
% 11.57/1.86    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.57/1.86    inference(cnf_transformation,[],[f31])).
% 11.57/1.86  fof(f31,plain,(
% 11.57/1.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.57/1.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 11.57/1.86  fof(f30,plain,(
% 11.57/1.86    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 11.57/1.86    introduced(choice_axiom,[])).
% 11.57/1.86  fof(f29,plain,(
% 11.57/1.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.57/1.86    inference(rectify,[],[f28])).
% 11.57/1.86  fof(f28,plain,(
% 11.57/1.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.57/1.86    inference(flattening,[],[f27])).
% 11.57/1.86  fof(f27,plain,(
% 11.57/1.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.57/1.86    inference(nnf_transformation,[],[f2])).
% 11.57/1.86  fof(f2,axiom,(
% 11.57/1.86    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.57/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 11.57/1.86  fof(f6219,plain,(
% 11.57/1.86    r2_hidden(sK0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl6_23),
% 11.57/1.86    inference(avatar_component_clause,[],[f6217])).
% 11.57/1.86  fof(f6217,plain,(
% 11.57/1.86    spl6_23 <=> r2_hidden(sK0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 11.57/1.86    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 11.57/1.86  fof(f6247,plain,(
% 11.57/1.86    spl6_23 | ~spl6_1 | ~spl6_3),
% 11.57/1.86    inference(avatar_split_clause,[],[f6246,f334,f249,f6217])).
% 11.57/1.86  fof(f249,plain,(
% 11.57/1.86    spl6_1 <=> r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.86    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 11.57/1.86  fof(f334,plain,(
% 11.57/1.86    spl6_3 <=> r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 11.57/1.86    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 11.57/1.86  fof(f6246,plain,(
% 11.57/1.86    r2_hidden(sK0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | (~spl6_1 | ~spl6_3)),
% 11.57/1.86    inference(forward_demodulation,[],[f335,f1362])).
% 11.57/1.86  fof(f1362,plain,(
% 11.57/1.86    sK0 = sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_1),
% 11.57/1.86    inference(unit_resulting_resolution,[],[f251,f66])).
% 11.57/1.86  fof(f251,plain,(
% 11.57/1.86    r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_1),
% 11.57/1.86    inference(avatar_component_clause,[],[f249])).
% 11.57/1.86  fof(f335,plain,(
% 11.57/1.86    r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl6_3),
% 11.57/1.86    inference(avatar_component_clause,[],[f334])).
% 11.57/1.86  fof(f6210,plain,(
% 11.57/1.86    ~spl6_1 | spl6_2),
% 11.57/1.86    inference(avatar_contradiction_clause,[],[f6209])).
% 11.57/1.86  fof(f6209,plain,(
% 11.57/1.86    $false | (~spl6_1 | spl6_2)),
% 11.57/1.86    inference(subsumption_resolution,[],[f32,f6197])).
% 11.57/1.86  fof(f6197,plain,(
% 11.57/1.86    ~r2_hidden(sK0,sK1) | (~spl6_1 | spl6_2)),
% 11.57/1.86    inference(superposition,[],[f254,f1362])).
% 11.57/1.86  fof(f254,plain,(
% 11.57/1.86    ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | spl6_2),
% 11.57/1.86    inference(avatar_component_clause,[],[f253])).
% 11.57/1.86  fof(f253,plain,(
% 11.57/1.86    spl6_2 <=> r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 11.57/1.86    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 11.57/1.86  fof(f1162,plain,(
% 11.57/1.86    ~spl6_1 | ~spl6_2 | spl6_3),
% 11.57/1.86    inference(avatar_split_clause,[],[f463,f334,f253,f249])).
% 11.57/1.86  fof(f463,plain,(
% 11.57/1.86    r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.86    inference(equality_resolution,[],[f84])).
% 11.57/1.86  fof(f84,plain,(
% 11.57/1.86    ( ! [X2] : (k2_enumset1(sK0,sK0,sK0,sK0) != X2 | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2),sK1) | ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2),X2)) )),
% 11.57/1.86    inference(superposition,[],[f56,f53])).
% 11.57/1.86  fof(f53,plain,(
% 11.57/1.86    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 11.57/1.86    inference(cnf_transformation,[],[f31])).
% 11.57/1.86  fof(f56,plain,(
% 11.57/1.86    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 11.57/1.86    inference(definition_unfolding,[],[f33,f55,f37,f55])).
% 11.57/1.86  fof(f37,plain,(
% 11.57/1.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.57/1.86    inference(cnf_transformation,[],[f5])).
% 11.57/1.86  fof(f5,axiom,(
% 11.57/1.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.57/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 11.57/1.86  fof(f33,plain,(
% 11.57/1.86    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 11.57/1.86    inference(cnf_transformation,[],[f18])).
% 11.57/1.86  fof(f1160,plain,(
% 11.57/1.86    spl6_3 | spl6_1 | ~spl6_2),
% 11.57/1.86    inference(avatar_split_clause,[],[f1153,f253,f249,f334])).
% 11.57/1.86  fof(f1153,plain,(
% 11.57/1.86    r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | (spl6_1 | ~spl6_2)),
% 11.57/1.86    inference(unit_resulting_resolution,[],[f255,f250,f67])).
% 11.57/1.86  fof(f67,plain,(
% 11.57/1.86    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.57/1.86    inference(equality_resolution,[],[f50])).
% 11.57/1.86  fof(f50,plain,(
% 11.57/1.86    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 11.57/1.86    inference(cnf_transformation,[],[f31])).
% 11.57/1.86  fof(f250,plain,(
% 11.57/1.86    ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_1),
% 11.57/1.86    inference(avatar_component_clause,[],[f249])).
% 11.57/1.86  fof(f255,plain,(
% 11.57/1.86    r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~spl6_2),
% 11.57/1.86    inference(avatar_component_clause,[],[f253])).
% 11.57/1.86  fof(f337,plain,(
% 11.57/1.86    spl6_1 | ~spl6_3),
% 11.57/1.86    inference(avatar_split_clause,[],[f331,f334,f249])).
% 11.57/1.86  fof(f331,plain,(
% 11.57/1.86    ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.86    inference(equality_resolution,[],[f83])).
% 11.57/1.86  fof(f83,plain,(
% 11.57/1.86    ( ! [X1] : (k2_enumset1(sK0,sK0,sK0,sK0) != X1 | ~r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1),X1)) )),
% 11.57/1.86    inference(superposition,[],[f56,f52])).
% 11.57/1.86  fof(f52,plain,(
% 11.57/1.86    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 11.57/1.86    inference(cnf_transformation,[],[f31])).
% 11.57/1.86  fof(f256,plain,(
% 11.57/1.86    spl6_1 | spl6_2),
% 11.57/1.86    inference(avatar_split_clause,[],[f246,f253,f249])).
% 11.57/1.86  fof(f246,plain,(
% 11.57/1.86    r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 11.57/1.86    inference(equality_resolution,[],[f82])).
% 11.57/1.86  fof(f82,plain,(
% 11.57/1.86    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0),sK1) | r2_hidden(sK5(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0),X0)) )),
% 11.57/1.86    inference(superposition,[],[f56,f51])).
% 11.57/1.86  fof(f51,plain,(
% 11.57/1.86    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 11.57/1.86    inference(cnf_transformation,[],[f31])).
% 11.57/1.86  % SZS output end Proof for theBenchmark
% 11.57/1.86  % (27183)------------------------------
% 11.57/1.86  % (27183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.57/1.86  % (27183)Termination reason: Refutation
% 11.57/1.86  
% 11.57/1.86  % (27183)Memory used [KB]: 16758
% 11.57/1.86  % (27183)Time elapsed: 1.058 s
% 11.57/1.86  % (27183)------------------------------
% 11.57/1.86  % (27183)------------------------------
% 11.57/1.86  % (27140)Success in time 1.511 s
%------------------------------------------------------------------------------
