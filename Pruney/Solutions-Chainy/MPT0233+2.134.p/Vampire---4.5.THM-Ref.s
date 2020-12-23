%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:21 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 211 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  318 ( 461 expanded)
%              Number of equality atoms :  197 ( 316 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f131,f427,f430])).

fof(f430,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f117,f112,f426,f101])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f426,plain,
    ( r2_hidden(sK0,k2_tarski(sK2,sK3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl6_5
  <=> r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f112,plain,
    ( sK0 != sK2
    | spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f117,plain,
    ( sK0 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f427,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f421,f128,f424])).

fof(f128,plain,
    ( spl6_4
  <=> r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f421,plain,
    ( r2_hidden(sK0,k2_tarski(sK2,sK3))
    | ~ spl6_4 ),
    inference(resolution,[],[f418,f130])).

fof(f130,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f418,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X3))
      | r2_hidden(X1,k2_tarski(X2,X3)) ) ),
    inference(forward_demodulation,[],[f409,f76])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f409,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X1,k5_xboole_0(k2_tarski(X2,X3),k1_xboole_0))
      | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X3)) ) ),
    inference(superposition,[],[f369,f169])).

fof(f169,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k4_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f145,f156])).

fof(f156,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f153,f147])).

fof(f147,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f144,f76])).

fof(f144,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f79,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f65,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f153,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f79,f148])).

fof(f148,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f87,f147])).

fof(f145,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f79,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f369,plain,(
    ! [X2,X0,X1] : r2_hidden(X2,k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) ),
    inference(superposition,[],[f358,f315])).

fof(f315,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))) ),
    inference(superposition,[],[f96,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f74,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(definition_unfolding,[],[f59,f74,f77,f58])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f358,plain,(
    ! [X12,X10,X11] : r2_hidden(X12,k3_enumset1(X10,X10,X10,X11,X12)) ),
    inference(superposition,[],[f103,f343])).

fof(f343,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f85,f96])).

fof(f85,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))))) ),
    inference(definition_unfolding,[],[f61,f77,f78])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))) != X3 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f69,f77])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f131,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f126,f120,f128])).

fof(f120,plain,
    ( spl6_3
  <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f126,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))
    | ~ spl6_3 ),
    inference(resolution,[],[f124,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_tarski(sK0,sK1))
        | r1_tarski(X0,k2_tarski(sK2,sK3)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f47,f122])).

fof(f122,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f123,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f120])).

fof(f43,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f118,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f45,f115])).

fof(f45,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f44,f110])).

fof(f44,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:46:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.51  % (28124)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (28114)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (28107)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28102)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (28102)Refutation not found, incomplete strategy% (28102)------------------------------
% 0.22/0.53  % (28102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28102)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28102)Memory used [KB]: 1663
% 0.22/0.53  % (28102)Time elapsed: 0.104 s
% 0.22/0.53  % (28102)------------------------------
% 0.22/0.53  % (28102)------------------------------
% 0.22/0.54  % (28108)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (28103)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (28101)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (28128)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (28104)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (28105)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (28131)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (28116)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (28129)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (28119)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (28110)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (28117)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (28120)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (28111)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (28125)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (28121)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (28122)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (28109)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (28126)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (28126)Refutation not found, incomplete strategy% (28126)------------------------------
% 0.22/0.56  % (28126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28129)Refutation not found, incomplete strategy% (28129)------------------------------
% 0.22/0.56  % (28129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28128)Refutation not found, incomplete strategy% (28128)------------------------------
% 0.22/0.56  % (28128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28128)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28128)Memory used [KB]: 6268
% 0.22/0.56  % (28128)Time elapsed: 0.139 s
% 0.22/0.56  % (28128)------------------------------
% 0.22/0.56  % (28128)------------------------------
% 0.22/0.56  % (28130)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (28129)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28129)Memory used [KB]: 6268
% 0.22/0.56  % (28129)Time elapsed: 0.141 s
% 0.22/0.56  % (28129)------------------------------
% 0.22/0.56  % (28129)------------------------------
% 1.50/0.56  % (28132)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.56  % (28130)Refutation not found, incomplete strategy% (28130)------------------------------
% 1.50/0.56  % (28130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (28130)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (28130)Memory used [KB]: 6268
% 1.50/0.56  % (28130)Time elapsed: 0.136 s
% 1.50/0.56  % (28130)------------------------------
% 1.50/0.56  % (28130)------------------------------
% 1.50/0.56  % (28132)Refutation not found, incomplete strategy% (28132)------------------------------
% 1.50/0.56  % (28132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (28132)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (28132)Memory used [KB]: 1663
% 1.50/0.56  % (28132)Time elapsed: 0.001 s
% 1.50/0.56  % (28132)------------------------------
% 1.50/0.56  % (28132)------------------------------
% 1.50/0.56  % (28113)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.56  % (28112)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.56  % (28120)Refutation not found, incomplete strategy% (28120)------------------------------
% 1.50/0.56  % (28120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (28112)Refutation not found, incomplete strategy% (28112)------------------------------
% 1.50/0.57  % (28112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (28106)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.57  % (28126)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (28126)Memory used [KB]: 10746
% 1.50/0.57  % (28126)Time elapsed: 0.139 s
% 1.50/0.57  % (28126)------------------------------
% 1.50/0.57  % (28126)------------------------------
% 1.50/0.57  % (28120)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (28120)Memory used [KB]: 1663
% 1.50/0.57  % (28120)Time elapsed: 0.139 s
% 1.50/0.57  % (28120)------------------------------
% 1.50/0.57  % (28120)------------------------------
% 1.50/0.57  % (28115)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.59  % (28112)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (28112)Memory used [KB]: 6396
% 1.66/0.59  % (28112)Time elapsed: 0.154 s
% 1.66/0.59  % (28112)------------------------------
% 1.66/0.59  % (28112)------------------------------
% 1.66/0.59  % (28115)Refutation not found, incomplete strategy% (28115)------------------------------
% 1.66/0.59  % (28115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (28115)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (28115)Memory used [KB]: 1791
% 1.66/0.59  % (28115)Time elapsed: 0.144 s
% 1.66/0.59  % (28115)------------------------------
% 1.66/0.59  % (28115)------------------------------
% 1.66/0.59  % (28123)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.66/0.60  % (28125)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f431,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(avatar_sat_refutation,[],[f113,f118,f123,f131,f427,f430])).
% 1.66/0.60  fof(f430,plain,(
% 1.66/0.60    spl6_1 | spl6_2 | ~spl6_5),
% 1.66/0.60    inference(avatar_contradiction_clause,[],[f428])).
% 1.66/0.60  fof(f428,plain,(
% 1.66/0.60    $false | (spl6_1 | spl6_2 | ~spl6_5)),
% 1.66/0.60    inference(unit_resulting_resolution,[],[f117,f112,f426,f101])).
% 1.66/0.60  fof(f101,plain,(
% 1.66/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.66/0.60    inference(equality_resolution,[],[f50])).
% 1.66/0.60  fof(f50,plain,(
% 1.66/0.60    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.66/0.60    inference(cnf_transformation,[],[f37])).
% 1.66/0.60  fof(f37,plain,(
% 1.66/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.66/0.60  fof(f36,plain,(
% 1.66/0.60    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f35,plain,(
% 1.66/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.66/0.60    inference(rectify,[],[f34])).
% 1.66/0.60  fof(f34,plain,(
% 1.66/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.66/0.60    inference(flattening,[],[f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.66/0.60    inference(nnf_transformation,[],[f10])).
% 1.66/0.60  fof(f10,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.66/0.60  fof(f426,plain,(
% 1.66/0.60    r2_hidden(sK0,k2_tarski(sK2,sK3)) | ~spl6_5),
% 1.66/0.60    inference(avatar_component_clause,[],[f424])).
% 1.66/0.60  fof(f424,plain,(
% 1.66/0.60    spl6_5 <=> r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.66/0.60  fof(f112,plain,(
% 1.66/0.60    sK0 != sK2 | spl6_1),
% 1.66/0.60    inference(avatar_component_clause,[],[f110])).
% 1.66/0.60  fof(f110,plain,(
% 1.66/0.60    spl6_1 <=> sK0 = sK2),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.66/0.60  fof(f117,plain,(
% 1.66/0.60    sK0 != sK3 | spl6_2),
% 1.66/0.60    inference(avatar_component_clause,[],[f115])).
% 1.66/0.60  fof(f115,plain,(
% 1.66/0.60    spl6_2 <=> sK0 = sK3),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.66/0.60  fof(f427,plain,(
% 1.66/0.60    spl6_5 | ~spl6_4),
% 1.66/0.60    inference(avatar_split_clause,[],[f421,f128,f424])).
% 1.66/0.60  fof(f128,plain,(
% 1.66/0.60    spl6_4 <=> r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.66/0.60  fof(f421,plain,(
% 1.66/0.60    r2_hidden(sK0,k2_tarski(sK2,sK3)) | ~spl6_4),
% 1.66/0.60    inference(resolution,[],[f418,f130])).
% 1.66/0.60  fof(f130,plain,(
% 1.66/0.60    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) | ~spl6_4),
% 1.66/0.60    inference(avatar_component_clause,[],[f128])).
% 1.66/0.60  fof(f418,plain,(
% 1.66/0.60    ( ! [X2,X3,X1] : (~r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X3)) | r2_hidden(X1,k2_tarski(X2,X3))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f409,f76])).
% 1.66/0.60  fof(f76,plain,(
% 1.66/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.60    inference(cnf_transformation,[],[f7])).
% 1.66/0.60  fof(f7,axiom,(
% 1.66/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.66/0.60  fof(f409,plain,(
% 1.66/0.60    ( ! [X2,X3,X1] : (r2_hidden(X1,k5_xboole_0(k2_tarski(X2,X3),k1_xboole_0)) | ~r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X3))) )),
% 1.66/0.60    inference(superposition,[],[f369,f169])).
% 1.66/0.60  fof(f169,plain,(
% 1.66/0.60    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X3)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f145,f156])).
% 1.66/0.60  fof(f156,plain,(
% 1.66/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f153,f147])).
% 1.66/0.60  fof(f147,plain,(
% 1.66/0.60    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.66/0.60    inference(forward_demodulation,[],[f144,f76])).
% 1.66/0.60  fof(f144,plain,(
% 1.66/0.60    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.66/0.60    inference(superposition,[],[f79,f87])).
% 1.66/0.60  fof(f87,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f65,f62])).
% 1.66/0.60  fof(f62,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f6])).
% 1.66/0.60  fof(f6,axiom,(
% 1.66/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.60  fof(f65,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f5])).
% 1.66/0.60  fof(f5,axiom,(
% 1.66/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.66/0.60  fof(f79,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f63,f62])).
% 1.66/0.60  fof(f63,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.66/0.60  fof(f153,plain,(
% 1.66/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.66/0.60    inference(superposition,[],[f79,f148])).
% 1.66/0.60  fof(f148,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.66/0.60    inference(superposition,[],[f87,f147])).
% 1.66/0.60  fof(f145,plain,(
% 1.66/0.60    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.66/0.60    inference(superposition,[],[f79,f82])).
% 1.66/0.60  fof(f82,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f48,f62])).
% 1.66/0.60  fof(f48,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f29])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f4])).
% 1.66/0.60  fof(f4,axiom,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.66/0.60  fof(f369,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))) )),
% 1.66/0.60    inference(superposition,[],[f358,f315])).
% 1.66/0.60  fof(f315,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) )),
% 1.66/0.60    inference(superposition,[],[f96,f80])).
% 1.66/0.60  fof(f80,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f57,f77])).
% 1.66/0.60  fof(f77,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f56,f74,f58])).
% 1.66/0.60  fof(f58,plain,(
% 1.66/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f14])).
% 1.66/0.60  fof(f14,axiom,(
% 1.66/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.60  fof(f74,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f8])).
% 1.66/0.60  fof(f8,axiom,(
% 1.66/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.66/0.60  fof(f56,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f11])).
% 1.66/0.60  fof(f11,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.66/0.60  fof(f57,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,axiom,(
% 1.66/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.60  fof(f96,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f75,f78])).
% 1.66/0.60  fof(f78,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f59,f74,f77,f58])).
% 1.66/0.60  fof(f59,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f13])).
% 1.66/0.60  fof(f13,axiom,(
% 1.66/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.66/0.60  fof(f75,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f17,axiom,(
% 1.66/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.66/0.60  fof(f358,plain,(
% 1.66/0.60    ( ! [X12,X10,X11] : (r2_hidden(X12,k3_enumset1(X10,X10,X10,X11,X12))) )),
% 1.66/0.60    inference(superposition,[],[f103,f343])).
% 1.66/0.60  fof(f343,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f85,f96])).
% 1.66/0.60  fof(f85,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f61,f77,f78])).
% 1.66/0.60  fof(f61,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f16])).
% 1.66/0.60  fof(f16,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.66/0.60  fof(f103,plain,(
% 1.66/0.60    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))))) )),
% 1.66/0.60    inference(equality_resolution,[],[f102])).
% 1.66/0.60  fof(f102,plain,(
% 1.66/0.60    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))) != X3) )),
% 1.66/0.60    inference(equality_resolution,[],[f92])).
% 1.66/0.60  fof(f92,plain,(
% 1.66/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 1.66/0.60    inference(definition_unfolding,[],[f69,f77])).
% 1.66/0.60  fof(f69,plain,(
% 1.66/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.66/0.60    inference(cnf_transformation,[],[f42])).
% 1.66/0.60  fof(f42,plain,(
% 1.66/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.66/0.60  fof(f41,plain,(
% 1.66/0.60    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f40,plain,(
% 1.66/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.66/0.60    inference(rectify,[],[f39])).
% 1.66/0.60  fof(f39,plain,(
% 1.66/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.66/0.60    inference(flattening,[],[f38])).
% 1.66/0.60  fof(f38,plain,(
% 1.66/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.66/0.60    inference(nnf_transformation,[],[f30])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.66/0.60    inference(ennf_transformation,[],[f9])).
% 1.66/0.60  fof(f9,axiom,(
% 1.66/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.66/0.60  fof(f131,plain,(
% 1.66/0.60    spl6_4 | ~spl6_3),
% 1.66/0.60    inference(avatar_split_clause,[],[f126,f120,f128])).
% 1.66/0.60  fof(f120,plain,(
% 1.66/0.60    spl6_3 <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.66/0.60  fof(f126,plain,(
% 1.66/0.60    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) | ~spl6_3),
% 1.66/0.60    inference(resolution,[],[f124,f83])).
% 1.66/0.60  fof(f83,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f49,f58])).
% 1.66/0.60  fof(f49,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f22])).
% 1.66/0.60  fof(f22,axiom,(
% 1.66/0.60    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.66/0.60  fof(f124,plain,(
% 1.66/0.60    ( ! [X0] : (~r1_tarski(X0,k2_tarski(sK0,sK1)) | r1_tarski(X0,k2_tarski(sK2,sK3))) ) | ~spl6_3),
% 1.66/0.60    inference(resolution,[],[f47,f122])).
% 1.66/0.60  fof(f122,plain,(
% 1.66/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) | ~spl6_3),
% 1.66/0.60    inference(avatar_component_clause,[],[f120])).
% 1.66/0.60  fof(f47,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f28])).
% 1.66/0.60  fof(f28,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.60    inference(flattening,[],[f27])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.60    inference(ennf_transformation,[],[f3])).
% 1.66/0.60  fof(f3,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.66/0.60  fof(f123,plain,(
% 1.66/0.60    spl6_3),
% 1.66/0.60    inference(avatar_split_clause,[],[f43,f120])).
% 1.66/0.60  fof(f43,plain,(
% 1.66/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.66/0.60    inference(cnf_transformation,[],[f32])).
% 1.66/0.60  fof(f32,plain,(
% 1.66/0.60    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).
% 1.66/0.60  fof(f31,plain,(
% 1.66/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f26,plain,(
% 1.66/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.66/0.60    inference(ennf_transformation,[],[f24])).
% 1.66/0.60  fof(f24,negated_conjecture,(
% 1.66/0.60    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.66/0.60    inference(negated_conjecture,[],[f23])).
% 1.66/0.60  fof(f23,conjecture,(
% 1.66/0.60    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.66/0.60  fof(f118,plain,(
% 1.66/0.60    ~spl6_2),
% 1.66/0.60    inference(avatar_split_clause,[],[f45,f115])).
% 1.66/0.60  fof(f45,plain,(
% 1.66/0.60    sK0 != sK3),
% 1.66/0.60    inference(cnf_transformation,[],[f32])).
% 1.66/0.60  fof(f113,plain,(
% 1.66/0.60    ~spl6_1),
% 1.66/0.60    inference(avatar_split_clause,[],[f44,f110])).
% 1.66/0.60  fof(f44,plain,(
% 1.66/0.60    sK0 != sK2),
% 1.66/0.60    inference(cnf_transformation,[],[f32])).
% 1.66/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (28125)------------------------------
% 1.66/0.60  % (28125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (28125)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (28125)Memory used [KB]: 11001
% 1.66/0.60  % (28125)Time elapsed: 0.179 s
% 1.66/0.60  % (28125)------------------------------
% 1.66/0.60  % (28125)------------------------------
% 1.66/0.60  % (28100)Success in time 0.221 s
%------------------------------------------------------------------------------
