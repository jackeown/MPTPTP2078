%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:59 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 233 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  271 ( 626 expanded)
%              Number of equality atoms :  148 ( 327 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f715,f716,f933])).

fof(f933,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | ~ spl6_5 ),
    inference(resolution,[],[f728,f213])).

fof(f213,plain,(
    ! [X4,X2,X3] : ~ sP0(X2,X3,X4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f112,f187])).

fof(f187,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f119,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f119,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X7) ),
    inference(resolution,[],[f110,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f110,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(resolution,[],[f109,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f109,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f92,f74])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) != X1
      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(resolution,[],[f76,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f112,plain,(
    ! [X4,X2,X3] : ~ sP0(X2,X3,X4,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X0,X1,X5,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f728,plain,
    ( sP0(sK2,sK2,sK2,k1_xboole_0)
    | ~ spl6_5 ),
    inference(superposition,[],[f91,f504])).

fof(f504,plain,
    ( k1_xboole_0 = k2_tarski(sK2,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl6_5
  <=> k1_xboole_0 = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f91,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f84,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f57])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f716,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f652,f502,f498])).

fof(f498,plain,
    ( spl6_4
  <=> k1_xboole_0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f652,plain,
    ( k1_xboole_0 = k2_tarski(sK2,sK2)
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f651])).

fof(f651,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2))
    | k1_xboole_0 = k2_tarski(sK2,sK2)
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f73,f452])).

fof(f452,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))
      | k1_xboole_0 = k2_tarski(X1,X1)
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(forward_demodulation,[],[f451,f75])).

fof(f75,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f451,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1))))
      | k1_xboole_0 = k2_tarski(X1,X1)
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(forward_demodulation,[],[f443,f71])).

fof(f443,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | k1_xboole_0 = k2_tarski(X1,X1)
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(superposition,[],[f371,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(superposition,[],[f72,f71])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_enumset1(X0,X0,X1,X2),k2_tarski(X3,X3))) ),
    inference(definition_unfolding,[],[f58,f45,f57,f44])).

fof(f45,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f371,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(superposition,[],[f78,f75])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f45,f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f73,plain,(
    k1_setfam_1(k2_tarski(sK1,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f41,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f28])).

fof(f28,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f715,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f517,f213])).

fof(f517,plain,
    ( sP0(sK1,sK1,sK1,k1_xboole_0)
    | ~ spl6_4 ),
    inference(superposition,[],[f91,f500])).

fof(f500,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:16:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.29/0.52  % (22600)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.53  % (22592)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (22582)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (22583)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.53  % (22586)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (22584)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (22582)Refutation not found, incomplete strategy% (22582)------------------------------
% 1.29/0.53  % (22582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (22582)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (22582)Memory used [KB]: 6268
% 1.29/0.53  % (22582)Time elapsed: 0.112 s
% 1.29/0.53  % (22582)------------------------------
% 1.29/0.53  % (22582)------------------------------
% 1.29/0.53  % (22600)Refutation not found, incomplete strategy% (22600)------------------------------
% 1.29/0.53  % (22600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (22600)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (22600)Memory used [KB]: 10746
% 1.29/0.53  % (22600)Time elapsed: 0.069 s
% 1.29/0.53  % (22600)------------------------------
% 1.29/0.53  % (22600)------------------------------
% 1.29/0.53  % (22580)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (22591)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (22580)Refutation not found, incomplete strategy% (22580)------------------------------
% 1.29/0.54  % (22580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22580)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22580)Memory used [KB]: 10618
% 1.29/0.54  % (22580)Time elapsed: 0.119 s
% 1.29/0.54  % (22580)------------------------------
% 1.29/0.54  % (22580)------------------------------
% 1.29/0.54  % (22581)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (22598)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.54  % (22598)Refutation not found, incomplete strategy% (22598)------------------------------
% 1.29/0.54  % (22598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22598)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22598)Memory used [KB]: 10746
% 1.29/0.54  % (22598)Time elapsed: 0.126 s
% 1.29/0.54  % (22598)------------------------------
% 1.29/0.54  % (22598)------------------------------
% 1.29/0.54  % (22588)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.54  % (22585)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (22588)Refutation not found, incomplete strategy% (22588)------------------------------
% 1.29/0.54  % (22588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22590)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (22604)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.55  % (22605)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.55  % (22596)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.55  % (22588)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (22588)Memory used [KB]: 10618
% 1.29/0.55  % (22588)Time elapsed: 0.124 s
% 1.29/0.55  % (22588)------------------------------
% 1.29/0.55  % (22588)------------------------------
% 1.29/0.55  % (22599)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.55  % (22597)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (22603)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.55  % (22587)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.55  % (22599)Refutation not found, incomplete strategy% (22599)------------------------------
% 1.53/0.55  % (22599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (22579)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.53/0.55  % (22587)Refutation not found, incomplete strategy% (22587)------------------------------
% 1.53/0.55  % (22587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (22587)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (22587)Memory used [KB]: 10618
% 1.53/0.55  % (22587)Time elapsed: 0.133 s
% 1.53/0.55  % (22587)------------------------------
% 1.53/0.55  % (22587)------------------------------
% 1.53/0.55  % (22586)Refutation not found, incomplete strategy% (22586)------------------------------
% 1.53/0.55  % (22586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (22586)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (22586)Memory used [KB]: 10618
% 1.53/0.55  % (22586)Time elapsed: 0.129 s
% 1.53/0.55  % (22586)------------------------------
% 1.53/0.55  % (22586)------------------------------
% 1.53/0.55  % (22599)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (22599)Memory used [KB]: 1663
% 1.53/0.55  % (22599)Time elapsed: 0.135 s
% 1.53/0.55  % (22599)------------------------------
% 1.53/0.55  % (22599)------------------------------
% 1.53/0.55  % (22593)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.55  % (22607)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.56  % (22589)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (22589)Refutation not found, incomplete strategy% (22589)------------------------------
% 1.53/0.56  % (22589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22589)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22589)Memory used [KB]: 10618
% 1.53/0.56  % (22589)Time elapsed: 0.147 s
% 1.53/0.56  % (22589)------------------------------
% 1.53/0.56  % (22589)------------------------------
% 1.53/0.56  % (22595)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.56  % (22601)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.56  % (22595)Refutation not found, incomplete strategy% (22595)------------------------------
% 1.53/0.56  % (22595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22595)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22595)Memory used [KB]: 10618
% 1.53/0.56  % (22595)Time elapsed: 0.144 s
% 1.53/0.56  % (22595)------------------------------
% 1.53/0.56  % (22595)------------------------------
% 1.53/0.56  % (22601)Refutation not found, incomplete strategy% (22601)------------------------------
% 1.53/0.56  % (22601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22601)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22601)Memory used [KB]: 1663
% 1.53/0.56  % (22601)Time elapsed: 0.146 s
% 1.53/0.56  % (22601)------------------------------
% 1.53/0.56  % (22601)------------------------------
% 1.53/0.56  % (22578)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.56  % (22578)Refutation not found, incomplete strategy% (22578)------------------------------
% 1.53/0.56  % (22578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22602)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.56  % (22578)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22578)Memory used [KB]: 1663
% 1.53/0.56  % (22578)Time elapsed: 0.141 s
% 1.53/0.56  % (22578)------------------------------
% 1.53/0.56  % (22578)------------------------------
% 1.53/0.56  % (22594)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (22593)Refutation not found, incomplete strategy% (22593)------------------------------
% 1.53/0.56  % (22593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22593)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22593)Memory used [KB]: 6140
% 1.53/0.56  % (22593)Time elapsed: 0.146 s
% 1.53/0.56  % (22593)------------------------------
% 1.53/0.56  % (22593)------------------------------
% 1.53/0.57  % (22606)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.57  % (22603)Refutation not found, incomplete strategy% (22603)------------------------------
% 1.53/0.57  % (22603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (22603)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (22603)Memory used [KB]: 6268
% 1.53/0.57  % (22603)Time elapsed: 0.156 s
% 1.53/0.57  % (22603)------------------------------
% 1.53/0.57  % (22603)------------------------------
% 1.53/0.60  % (22590)Refutation found. Thanks to Tanya!
% 1.53/0.60  % SZS status Theorem for theBenchmark
% 1.53/0.60  % SZS output start Proof for theBenchmark
% 1.53/0.60  fof(f934,plain,(
% 1.53/0.60    $false),
% 1.53/0.60    inference(avatar_sat_refutation,[],[f715,f716,f933])).
% 1.53/0.60  fof(f933,plain,(
% 1.53/0.60    ~spl6_5),
% 1.53/0.60    inference(avatar_contradiction_clause,[],[f929])).
% 1.53/0.60  fof(f929,plain,(
% 1.53/0.60    $false | ~spl6_5),
% 1.53/0.60    inference(resolution,[],[f728,f213])).
% 1.53/0.60  fof(f213,plain,(
% 1.53/0.60    ( ! [X4,X2,X3] : (~sP0(X2,X3,X4,k1_xboole_0)) )),
% 1.53/0.60    inference(backward_demodulation,[],[f112,f187])).
% 1.53/0.60  fof(f187,plain,(
% 1.53/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.53/0.60    inference(superposition,[],[f119,f74])).
% 1.53/0.60  fof(f74,plain,(
% 1.53/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.53/0.60    inference(definition_unfolding,[],[f42,f47])).
% 1.53/0.60  fof(f47,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f5])).
% 1.53/0.60  fof(f5,axiom,(
% 1.53/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.53/0.60  fof(f42,plain,(
% 1.53/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f4])).
% 1.53/0.60  fof(f4,axiom,(
% 1.53/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.53/0.60  fof(f119,plain,(
% 1.53/0.60    ( ! [X7] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X7)) )),
% 1.53/0.60    inference(resolution,[],[f110,f54])).
% 1.53/0.60  fof(f54,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.53/0.60    inference(cnf_transformation,[],[f34])).
% 1.53/0.60  fof(f34,plain,(
% 1.53/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(nnf_transformation,[],[f6])).
% 1.53/0.60  fof(f6,axiom,(
% 1.53/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.53/0.60  fof(f110,plain,(
% 1.53/0.60    ( ! [X0] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 1.53/0.60    inference(resolution,[],[f109,f50])).
% 1.53/0.60  fof(f50,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f33])).
% 1.53/0.60  fof(f33,plain,(
% 1.53/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f32])).
% 1.53/0.60  fof(f32,plain,(
% 1.53/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f22,plain,(
% 1.53/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(ennf_transformation,[],[f19])).
% 1.53/0.60  fof(f19,plain,(
% 1.53/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(rectify,[],[f2])).
% 1.53/0.60  fof(f2,axiom,(
% 1.53/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.53/0.60  fof(f109,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.53/0.60    inference(equality_resolution,[],[f108])).
% 1.53/0.60  fof(f108,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.53/0.60    inference(superposition,[],[f92,f74])).
% 1.53/0.60  fof(f92,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) != X1 | ~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 1.53/0.60    inference(resolution,[],[f76,f55])).
% 1.53/0.60  fof(f55,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.53/0.60    inference(cnf_transformation,[],[f34])).
% 1.53/0.60  fof(f76,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.53/0.60    inference(definition_unfolding,[],[f49,f47])).
% 1.53/0.60  fof(f49,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f31])).
% 1.53/0.60  fof(f31,plain,(
% 1.53/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f30])).
% 1.53/0.60  fof(f30,plain,(
% 1.53/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f21,plain,(
% 1.53/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(ennf_transformation,[],[f18])).
% 1.53/0.60  fof(f18,plain,(
% 1.53/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(rectify,[],[f3])).
% 1.53/0.60  fof(f3,axiom,(
% 1.53/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.53/0.60  fof(f112,plain,(
% 1.53/0.60    ( ! [X4,X2,X3] : (~sP0(X2,X3,X4,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.53/0.60    inference(resolution,[],[f109,f83])).
% 1.53/0.60  fof(f83,plain,(
% 1.53/0.60    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X0,X1,X5,X3)) )),
% 1.53/0.60    inference(equality_resolution,[],[f60])).
% 1.53/0.60  fof(f60,plain,(
% 1.53/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f39])).
% 1.53/0.60  fof(f39,plain,(
% 1.53/0.60    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.53/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.53/0.60  fof(f38,plain,(
% 1.53/0.60    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f37,plain,(
% 1.53/0.60    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.53/0.60    inference(rectify,[],[f36])).
% 1.53/0.60  fof(f36,plain,(
% 1.53/0.60    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.53/0.60    inference(flattening,[],[f35])).
% 1.53/0.60  fof(f35,plain,(
% 1.53/0.60    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.53/0.60    inference(nnf_transformation,[],[f26])).
% 1.53/0.60  fof(f26,plain,(
% 1.53/0.60    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.53/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.53/0.60  fof(f728,plain,(
% 1.53/0.60    sP0(sK2,sK2,sK2,k1_xboole_0) | ~spl6_5),
% 1.53/0.60    inference(superposition,[],[f91,f504])).
% 1.53/0.60  fof(f504,plain,(
% 1.53/0.60    k1_xboole_0 = k2_tarski(sK2,sK2) | ~spl6_5),
% 1.53/0.60    inference(avatar_component_clause,[],[f502])).
% 1.53/0.60  fof(f502,plain,(
% 1.53/0.60    spl6_5 <=> k1_xboole_0 = k2_tarski(sK2,sK2)),
% 1.53/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.53/0.60  fof(f91,plain,(
% 1.53/0.60    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 1.53/0.60    inference(superposition,[],[f84,f71])).
% 1.53/0.60  fof(f71,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.53/0.60    inference(definition_unfolding,[],[f46,f57])).
% 1.53/0.60  fof(f57,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f12])).
% 1.53/0.60  fof(f12,axiom,(
% 1.53/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.60  fof(f46,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f11])).
% 1.53/0.60  fof(f11,axiom,(
% 1.53/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.61  fof(f84,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.53/0.61    inference(equality_resolution,[],[f80])).
% 1.53/0.61  fof(f80,plain,(
% 1.53/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.53/0.61    inference(definition_unfolding,[],[f67,f57])).
% 1.53/0.61  fof(f67,plain,(
% 1.53/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.53/0.61    inference(cnf_transformation,[],[f40])).
% 1.53/0.62  fof(f40,plain,(
% 1.53/0.62    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.53/0.62    inference(nnf_transformation,[],[f27])).
% 1.53/0.62  fof(f27,plain,(
% 1.53/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.53/0.62    inference(definition_folding,[],[f25,f26])).
% 1.53/0.62  fof(f25,plain,(
% 1.53/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.53/0.62    inference(ennf_transformation,[],[f7])).
% 1.53/0.62  fof(f7,axiom,(
% 1.53/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.53/0.62  fof(f716,plain,(
% 1.53/0.62    spl6_4 | spl6_5),
% 1.53/0.62    inference(avatar_split_clause,[],[f652,f502,f498])).
% 1.53/0.62  fof(f498,plain,(
% 1.53/0.62    spl6_4 <=> k1_xboole_0 = k2_tarski(sK1,sK1)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.53/0.62  fof(f652,plain,(
% 1.53/0.62    k1_xboole_0 = k2_tarski(sK2,sK2) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 1.53/0.62    inference(trivial_inequality_removal,[],[f651])).
% 1.53/0.62  fof(f651,plain,(
% 1.53/0.62    k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) | k1_xboole_0 = k2_tarski(sK2,sK2) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 1.53/0.62    inference(superposition,[],[f73,f452])).
% 1.53/0.62  fof(f452,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) | k1_xboole_0 = k2_tarski(X1,X1) | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 1.53/0.62    inference(forward_demodulation,[],[f451,f75])).
% 1.53/0.62  fof(f75,plain,(
% 1.53/0.62    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.53/0.62    inference(definition_unfolding,[],[f43,f44])).
% 1.53/0.62  fof(f44,plain,(
% 1.53/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f10])).
% 1.53/0.62  fof(f10,axiom,(
% 1.53/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.62  fof(f43,plain,(
% 1.53/0.62    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f15,axiom,(
% 1.53/0.62    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.53/0.62  fof(f451,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) | k1_xboole_0 = k2_tarski(X1,X1) | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 1.53/0.62    inference(forward_demodulation,[],[f443,f71])).
% 1.53/0.62  fof(f443,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = k2_tarski(X1,X1) | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 1.53/0.62    inference(superposition,[],[f371,f131])).
% 1.53/0.62  fof(f131,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 1.53/0.62    inference(superposition,[],[f72,f71])).
% 1.53/0.62  fof(f72,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_enumset1(X0,X0,X1,X2),k2_tarski(X3,X3)))) )),
% 1.53/0.62    inference(definition_unfolding,[],[f58,f45,f57,f44])).
% 1.53/0.62  fof(f45,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f13])).
% 1.53/0.62  fof(f13,axiom,(
% 1.53/0.62    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.53/0.62  fof(f58,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f8])).
% 1.53/0.62  fof(f8,axiom,(
% 1.53/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.53/0.62  fof(f371,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 1.53/0.62    inference(superposition,[],[f78,f75])).
% 1.53/0.62  fof(f78,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.62    inference(definition_unfolding,[],[f56,f45,f47])).
% 1.53/0.62  fof(f56,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f24])).
% 1.53/0.62  fof(f24,plain,(
% 1.53/0.62    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.53/0.62    inference(ennf_transformation,[],[f14])).
% 1.53/0.62  fof(f14,axiom,(
% 1.53/0.62    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.53/0.62  fof(f73,plain,(
% 1.53/0.62    k1_setfam_1(k2_tarski(sK1,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.53/0.62    inference(definition_unfolding,[],[f41,f47])).
% 1.53/0.62  fof(f41,plain,(
% 1.53/0.62    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.53/0.62    inference(cnf_transformation,[],[f29])).
% 1.53/0.62  fof(f29,plain,(
% 1.53/0.62    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.53/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f28])).
% 1.53/0.62  fof(f28,plain,(
% 1.53/0.62    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.53/0.62    introduced(choice_axiom,[])).
% 1.53/0.62  fof(f20,plain,(
% 1.53/0.62    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.53/0.62    inference(ennf_transformation,[],[f17])).
% 1.53/0.62  fof(f17,negated_conjecture,(
% 1.53/0.62    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.53/0.62    inference(negated_conjecture,[],[f16])).
% 1.53/0.62  fof(f16,conjecture,(
% 1.53/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.53/0.62  fof(f715,plain,(
% 1.53/0.62    ~spl6_4),
% 1.53/0.62    inference(avatar_contradiction_clause,[],[f711])).
% 1.53/0.62  fof(f711,plain,(
% 1.53/0.62    $false | ~spl6_4),
% 1.53/0.62    inference(resolution,[],[f517,f213])).
% 1.53/0.62  fof(f517,plain,(
% 1.53/0.62    sP0(sK1,sK1,sK1,k1_xboole_0) | ~spl6_4),
% 1.53/0.62    inference(superposition,[],[f91,f500])).
% 1.53/0.62  fof(f500,plain,(
% 1.53/0.62    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl6_4),
% 1.53/0.62    inference(avatar_component_clause,[],[f498])).
% 1.53/0.62  % SZS output end Proof for theBenchmark
% 1.53/0.62  % (22590)------------------------------
% 1.53/0.62  % (22590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.62  % (22590)Termination reason: Refutation
% 1.53/0.62  
% 1.53/0.62  % (22590)Memory used [KB]: 6652
% 1.53/0.62  % (22590)Time elapsed: 0.193 s
% 1.53/0.62  % (22590)------------------------------
% 1.53/0.62  % (22590)------------------------------
% 1.53/0.62  % (22577)Success in time 0.251 s
%------------------------------------------------------------------------------
