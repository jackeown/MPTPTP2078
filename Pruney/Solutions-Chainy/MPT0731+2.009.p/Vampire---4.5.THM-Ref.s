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
% DateTime   : Thu Dec  3 12:55:15 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  282 ( 519 expanded)
%              Number of equality atoms :  225 ( 433 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f157,f189])).

fof(f189,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f175,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X10,X5,X3,X1] : r2_hidden(X10,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X10,X8,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10) != X8 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X7 != X10
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f24,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f175,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f155,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f155,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_3
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f157,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f115,f83,f153])).

fof(f83,plain,
    ( spl2_1
  <=> sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f115,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f105,f66])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
        | r1_tarski(X0,sK0) )
    | ~ spl2_1 ),
    inference(superposition,[],[f31,f85])).

fof(f85,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f86,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f64,f83])).

fof(f64,plain,(
    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f26,f63])).

fof(f63,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f28,f62,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f60])).

fof(f29,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f26,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).

fof(f19,plain,
    ( ? [X0] : k1_ordinal1(X0) = X0
   => sK0 = k1_ordinal1(sK0) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : k1_ordinal1(X0) = X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (6117)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (6138)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.21/0.52  % (6134)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.21/0.52  % (6121)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.21/0.52  % (6134)Refutation not found, incomplete strategy% (6134)------------------------------
% 1.21/0.52  % (6134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (6134)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (6134)Memory used [KB]: 1791
% 1.21/0.52  % (6134)Time elapsed: 0.108 s
% 1.21/0.52  % (6134)------------------------------
% 1.21/0.52  % (6134)------------------------------
% 1.21/0.52  % (6121)Refutation not found, incomplete strategy% (6121)------------------------------
% 1.21/0.52  % (6121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (6121)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (6121)Memory used [KB]: 10618
% 1.21/0.52  % (6121)Time elapsed: 0.107 s
% 1.21/0.52  % (6121)------------------------------
% 1.21/0.52  % (6121)------------------------------
% 1.21/0.52  % (6115)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.52  % (6138)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.52  % SZS output start Proof for theBenchmark
% 1.21/0.52  fof(f190,plain,(
% 1.21/0.52    $false),
% 1.21/0.52    inference(avatar_sat_refutation,[],[f86,f157,f189])).
% 1.21/0.52  fof(f189,plain,(
% 1.21/0.52    ~spl2_3),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f188])).
% 1.21/0.52  fof(f188,plain,(
% 1.21/0.52    $false | ~spl2_3),
% 1.21/0.52    inference(subsumption_resolution,[],[f175,f66])).
% 1.21/0.52  fof(f66,plain,(
% 1.21/0.52    ( ! [X6,X4,X2,X0,X10,X5,X3,X1] : (r2_hidden(X10,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10))) )),
% 1.21/0.52    inference(equality_resolution,[],[f65])).
% 1.21/0.52  fof(f65,plain,(
% 1.21/0.52    ( ! [X6,X4,X2,X0,X10,X8,X5,X3,X1] : (r2_hidden(X10,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10) != X8) )),
% 1.21/0.52    inference(equality_resolution,[],[f46])).
% 1.21/0.52  fof(f46,plain,(
% 1.21/0.52    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X7 != X10 | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.21/0.52    inference(cnf_transformation,[],[f25])).
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | (((sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8))) => (((sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.21/0.53    inference(rectify,[],[f22])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.21/0.53    inference(flattening,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.21/0.53    inference(nnf_transformation,[],[f18])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.21/0.53    inference(ennf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,axiom,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 1.21/0.53  fof(f175,plain,(
% 1.21/0.53    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_3),
% 1.21/0.53    inference(resolution,[],[f155,f32])).
% 1.21/0.53  fof(f32,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f17])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f12])).
% 1.21/0.53  fof(f12,axiom,(
% 1.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.21/0.53  fof(f155,plain,(
% 1.21/0.53    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK0) | ~spl2_3),
% 1.21/0.53    inference(avatar_component_clause,[],[f153])).
% 1.21/0.53  fof(f153,plain,(
% 1.21/0.53    spl2_3 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK0)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.21/0.53  fof(f157,plain,(
% 1.21/0.53    spl2_3 | ~spl2_1),
% 1.21/0.53    inference(avatar_split_clause,[],[f115,f83,f153])).
% 1.21/0.53  fof(f83,plain,(
% 1.21/0.53    spl2_1 <=> sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.21/0.53  fof(f115,plain,(
% 1.21/0.53    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK0) | ~spl2_1),
% 1.21/0.53    inference(resolution,[],[f105,f66])).
% 1.21/0.53  fof(f105,plain,(
% 1.21/0.53    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r1_tarski(X0,sK0)) ) | ~spl2_1),
% 1.21/0.53    inference(superposition,[],[f31,f85])).
% 1.21/0.53  fof(f85,plain,(
% 1.21/0.53    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl2_1),
% 1.21/0.53    inference(avatar_component_clause,[],[f83])).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f8])).
% 1.21/0.53  fof(f8,axiom,(
% 1.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.21/0.53  fof(f86,plain,(
% 1.21/0.53    spl2_1),
% 1.21/0.53    inference(avatar_split_clause,[],[f64,f83])).
% 1.21/0.53  fof(f64,plain,(
% 1.21/0.53    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.21/0.53    inference(definition_unfolding,[],[f26,f63])).
% 1.21/0.53  fof(f63,plain,(
% 1.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f28,f62,f61])).
% 1.21/0.53  fof(f61,plain,(
% 1.21/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f27,f60])).
% 1.21/0.53  fof(f60,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f30,f59])).
% 1.21/0.53  fof(f59,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f33,f58])).
% 1.21/0.53  fof(f58,plain,(
% 1.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f34,f57])).
% 1.21/0.53  fof(f57,plain,(
% 1.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f35,f56])).
% 1.21/0.53  fof(f56,plain,(
% 1.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f36,f37])).
% 1.21/0.53  fof(f37,plain,(
% 1.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.21/0.53  fof(f36,plain,(
% 1.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f6])).
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.21/0.53  fof(f35,plain,(
% 1.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.21/0.53  fof(f34,plain,(
% 1.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.21/0.53  fof(f33,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.21/0.53  fof(f30,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.21/0.53  fof(f62,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f29,f60])).
% 1.21/0.53  fof(f29,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f9])).
% 1.21/0.53  fof(f9,axiom,(
% 1.21/0.53    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 1.21/0.53  fof(f28,plain,(
% 1.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,axiom,(
% 1.21/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    sK0 = k1_ordinal1(sK0)),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    sK0 = k1_ordinal1(sK0)),
% 1.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ? [X0] : k1_ordinal1(X0) = X0 => sK0 = k1_ordinal1(sK0)),
% 1.21/0.53    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    ? [X0] : k1_ordinal1(X0) = X0),
% 1.21/0.53    inference(ennf_transformation,[],[f14])).
% 1.21/0.53  fof(f14,negated_conjecture,(
% 1.21/0.53    ~! [X0] : k1_ordinal1(X0) != X0),
% 1.21/0.53    inference(negated_conjecture,[],[f13])).
% 1.21/0.53  fof(f13,conjecture,(
% 1.21/0.53    ! [X0] : k1_ordinal1(X0) != X0),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 1.21/0.53  % SZS output end Proof for theBenchmark
% 1.21/0.53  % (6138)------------------------------
% 1.21/0.53  % (6138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (6138)Termination reason: Refutation
% 1.21/0.53  
% 1.21/0.53  % (6138)Memory used [KB]: 6268
% 1.21/0.53  % (6138)Time elapsed: 0.109 s
% 1.21/0.53  % (6138)------------------------------
% 1.21/0.53  % (6138)------------------------------
% 1.21/0.53  % (6133)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.21/0.53  % (6109)Success in time 0.166 s
%------------------------------------------------------------------------------
