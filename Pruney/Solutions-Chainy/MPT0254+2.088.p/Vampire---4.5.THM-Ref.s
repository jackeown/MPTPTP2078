%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 503 expanded)
%              Number of leaves         :   34 ( 170 expanded)
%              Depth                    :   19
%              Number of atoms          :  289 ( 771 expanded)
%              Number of equality atoms :  113 ( 514 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f781,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f613,f707,f724,f755,f780])).

fof(f780,plain,
    ( ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(resolution,[],[f768,f93])).

fof(f93,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f768,plain,
    ( ! [X0] : ~ sP0(X0,sK2,sK2,sK2)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f766,f169])).

fof(f169,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_2
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f766,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK2,sK2,sK2)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f617,f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f617,plain,
    ( sP1(sK2,sK2,sK2,k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl6_5
  <=> sP1(sK2,sK2,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f755,plain,
    ( spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f750,f656,f616])).

fof(f656,plain,
    ( spl6_9
  <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f750,plain,
    ( sP1(sK2,sK2,sK2,k1_xboole_0)
    | ~ spl6_9 ),
    inference(superposition,[],[f96,f658])).

fof(f658,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f656])).

fof(f96,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f31,f33,f32])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f724,plain,
    ( spl6_9
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f723,f610,f656])).

fof(f610,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f723,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f717,f96])).

fof(f717,plain,
    ( ! [X0] :
        ( ~ sP1(sK2,sK2,sK2,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f716,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f716,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0)
        | ~ sP1(sK2,sK2,sK2,X0) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f715,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f715,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))
        | ~ sP1(sK2,sK2,sK2,X0) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f714,f56])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f714,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)
        | ~ sP1(sK2,sK2,sK2,X0) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f710,f50])).

fof(f710,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0))
        | ~ sP1(sK2,sK2,sK2,X0) )
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f570,f612])).

fof(f612,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f610])).

fof(f570,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,sK3),k5_xboole_0(X0,sK3))
      | ~ sP1(sK2,sK2,sK2,X0) ) ),
    inference(forward_demodulation,[],[f569,f56])).

fof(f569,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,sK3),k3_xboole_0(X0,sK3))
      | ~ sP1(sK2,sK2,sK2,X0) ) ),
    inference(forward_demodulation,[],[f565,f90])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f61,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f84])).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f565,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
      | ~ sP1(sK2,sK2,sK2,X0) ) ),
    inference(superposition,[],[f88,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f77,f84])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f47,f86,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f85])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f35])).

fof(f35,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f707,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f700,f96])).

fof(f700,plain,
    ( ! [X21] : ~ sP1(sK2,sK2,sK2,X21)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f699,f608])).

fof(f608,plain,
    ( ! [X1] :
        ( ~ sP1(sK2,sK2,sK2,X1)
        | ~ r1_tarski(X1,sK3) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl6_3
  <=> ! [X1] :
        ( ~ sP1(sK2,sK2,sK2,X1)
        | ~ r1_tarski(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f699,plain,(
    ! [X21] :
      ( r1_tarski(X21,sK3)
      | ~ sP1(sK2,sK2,sK2,X21) ) ),
    inference(subsumption_resolution,[],[f687,f106])).

fof(f106,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f687,plain,(
    ! [X21] :
      ( ~ r1_tarski(k3_xboole_0(X21,sK3),sK3)
      | r1_tarski(X21,sK3)
      | ~ sP1(sK2,sK2,sK2,X21) ) ),
    inference(superposition,[],[f406,f641])).

fof(f641,plain,(
    ! [X10] :
      ( k3_xboole_0(X10,sK3) = k5_xboole_0(X10,sK3)
      | ~ sP1(sK2,sK2,sK2,X10) ) ),
    inference(forward_demodulation,[],[f593,f50])).

fof(f593,plain,(
    ! [X10] :
      ( k5_xboole_0(X10,sK3) = k5_xboole_0(k3_xboole_0(X10,sK3),k1_xboole_0)
      | ~ sP1(sK2,sK2,sK2,X10) ) ),
    inference(superposition,[],[f247,f570])).

fof(f247,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f229,f116])).

fof(f116,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f56,f50])).

fof(f229,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f66,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f406,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k5_xboole_0(X8,X7),X7)
      | r1_tarski(X8,X7) ) ),
    inference(superposition,[],[f194,f251])).

fof(f251,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f247,f56])).

fof(f194,plain,(
    ! [X19,X18] :
      ( r1_tarski(k5_xboole_0(X19,X18),X19)
      | ~ r1_tarski(X18,X19) ) ),
    inference(superposition,[],[f139,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f139,plain,(
    ! [X2,X1] : r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f89,f55])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f613,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f605,f610,f607])).

fof(f605,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK3
      | ~ sP1(sK2,sK2,sK2,X1)
      | ~ r1_tarski(X1,sK3) ) ),
    inference(forward_demodulation,[],[f576,f247])).

fof(f576,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X1,sK3))
      | ~ sP1(sK2,sK2,sK2,X1)
      | ~ r1_tarski(X1,sK3) ) ),
    inference(superposition,[],[f570,f64])).

fof(f172,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f171,f168])).

fof(f171,plain,(
    ! [X9] : ~ r2_hidden(X9,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f163,f133])).

fof(f133,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f124,f50])).

fof(f124,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f163,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X8) ) ),
    inference(superposition,[],[f63,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f52,f54])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (21033)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (21025)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (21017)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (21032)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (21023)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21040)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (21022)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21024)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (21021)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (21011)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (21031)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (21012)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21015)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21014)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (21034)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21013)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21034)Refutation not found, incomplete strategy% (21034)------------------------------
% 0.21/0.54  % (21034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21034)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21034)Memory used [KB]: 1663
% 0.21/0.54  % (21034)Time elapsed: 0.138 s
% 0.21/0.54  % (21034)------------------------------
% 0.21/0.54  % (21034)------------------------------
% 0.21/0.54  % (21035)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21016)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (21020)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (21021)Refutation not found, incomplete strategy% (21021)------------------------------
% 0.21/0.54  % (21021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21021)Memory used [KB]: 10618
% 0.21/0.54  % (21021)Time elapsed: 0.135 s
% 0.21/0.54  % (21021)------------------------------
% 0.21/0.54  % (21021)------------------------------
% 0.21/0.54  % (21018)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (21037)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21027)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (21039)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (21038)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21036)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21026)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (21029)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (21026)Refutation not found, incomplete strategy% (21026)------------------------------
% 0.21/0.55  % (21026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21026)Memory used [KB]: 6140
% 0.21/0.55  % (21026)Time elapsed: 0.002 s
% 0.21/0.55  % (21026)------------------------------
% 0.21/0.55  % (21026)------------------------------
% 0.21/0.55  % (21019)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21031)Refutation not found, incomplete strategy% (21031)------------------------------
% 0.21/0.55  % (21031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21031)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21031)Memory used [KB]: 10746
% 0.21/0.55  % (21031)Time elapsed: 0.153 s
% 0.21/0.55  % (21031)------------------------------
% 0.21/0.55  % (21031)------------------------------
% 0.21/0.55  % (21030)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (21028)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (21028)Refutation not found, incomplete strategy% (21028)------------------------------
% 0.21/0.56  % (21028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21028)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21028)Memory used [KB]: 10618
% 0.21/0.56  % (21028)Time elapsed: 0.159 s
% 0.21/0.56  % (21028)------------------------------
% 0.21/0.56  % (21028)------------------------------
% 0.21/0.56  % (21015)Refutation not found, incomplete strategy% (21015)------------------------------
% 0.21/0.56  % (21015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21015)Memory used [KB]: 6396
% 0.21/0.56  % (21015)Time elapsed: 0.141 s
% 0.21/0.56  % (21015)------------------------------
% 0.21/0.56  % (21015)------------------------------
% 0.21/0.57  % (21038)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f781,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f172,f613,f707,f724,f755,f780])).
% 0.21/0.57  fof(f780,plain,(
% 0.21/0.57    ~spl6_2 | ~spl6_5),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f774])).
% 0.21/0.57  fof(f774,plain,(
% 0.21/0.57    $false | (~spl6_2 | ~spl6_5)),
% 0.21/0.57    inference(resolution,[],[f768,f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 0.21/0.57    inference(equality_resolution,[],[f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.57    inference(rectify,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 0.21/0.57    inference(flattening,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.57  fof(f768,plain,(
% 0.21/0.57    ( ! [X0] : (~sP0(X0,sK2,sK2,sK2)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.57    inference(subsumption_resolution,[],[f766,f169])).
% 0.21/0.57  fof(f169,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f168])).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    spl6_2 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.57  fof(f766,plain,(
% 0.21/0.57    ( ! [X0] : (~sP0(X0,sK2,sK2,sK2) | r2_hidden(X0,k1_xboole_0)) ) | ~spl6_5),
% 0.21/0.57    inference(resolution,[],[f617,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.57    inference(rectify,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.57    inference(nnf_transformation,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.57  fof(f617,plain,(
% 0.21/0.57    sP1(sK2,sK2,sK2,k1_xboole_0) | ~spl6_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f616])).
% 0.21/0.57  fof(f616,plain,(
% 0.21/0.57    spl6_5 <=> sP1(sK2,sK2,sK2,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.57  fof(f755,plain,(
% 0.21/0.57    spl6_5 | ~spl6_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f750,f656,f616])).
% 0.21/0.57  fof(f656,plain,(
% 0.21/0.57    spl6_9 <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.57  fof(f750,plain,(
% 0.21/0.57    sP1(sK2,sK2,sK2,k1_xboole_0) | ~spl6_9),
% 0.21/0.57    inference(superposition,[],[f96,f658])).
% 0.21/0.57  fof(f658,plain,(
% 0.21/0.57    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f656])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.21/0.57    inference(equality_resolution,[],[f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.57    inference(definition_unfolding,[],[f76,f84])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f65,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f67,f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f78,f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f79,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.57    inference(cnf_transformation,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.57    inference(nnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 0.21/0.57    inference(definition_folding,[],[f31,f33,f32])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.57  fof(f724,plain,(
% 0.21/0.57    spl6_9 | ~spl6_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f723,f610,f656])).
% 0.21/0.57  fof(f610,plain,(
% 0.21/0.57    spl6_4 <=> k1_xboole_0 = sK3),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.57  fof(f723,plain,(
% 0.21/0.57    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_4),
% 0.21/0.57    inference(resolution,[],[f717,f96])).
% 0.21/0.57  fof(f717,plain,(
% 0.21/0.57    ( ! [X0] : (~sP1(sK2,sK2,sK2,X0) | k1_xboole_0 = X0) ) | ~spl6_4),
% 0.21/0.57    inference(forward_demodulation,[],[f716,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.57  fof(f716,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0) | ~sP1(sK2,sK2,sK2,X0)) ) | ~spl6_4),
% 0.21/0.57    inference(forward_demodulation,[],[f715,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.57  fof(f715,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) | ~sP1(sK2,sK2,sK2,X0)) ) | ~spl6_4),
% 0.21/0.57    inference(forward_demodulation,[],[f714,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.57  fof(f714,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) | ~sP1(sK2,sK2,sK2,X0)) ) | ~spl6_4),
% 0.21/0.57    inference(forward_demodulation,[],[f710,f50])).
% 0.21/0.57  fof(f710,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0)) | ~sP1(sK2,sK2,sK2,X0)) ) | ~spl6_4),
% 0.21/0.57    inference(backward_demodulation,[],[f570,f612])).
% 0.21/0.57  fof(f612,plain,(
% 0.21/0.57    k1_xboole_0 = sK3 | ~spl6_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f610])).
% 0.21/0.57  fof(f570,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,sK3),k5_xboole_0(X0,sK3)) | ~sP1(sK2,sK2,sK2,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f569,f56])).
% 0.21/0.57  fof(f569,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,sK3),k3_xboole_0(X0,sK3)) | ~sP1(sK2,sK2,sK2,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f565,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f61,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f58,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f59,f84])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.57  fof(f565,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) | ~sP1(sK2,sK2,sK2,X0)) )),
% 0.21/0.57    inference(superposition,[],[f88,f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f77,f84])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f46])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.21/0.57    inference(definition_unfolding,[],[f47,f86,f87])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f51,f85])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.57    inference(ennf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.57    inference(negated_conjecture,[],[f24])).
% 0.21/0.57  fof(f24,conjecture,(
% 0.21/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.57  fof(f707,plain,(
% 0.21/0.57    ~spl6_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f706])).
% 0.21/0.57  fof(f706,plain,(
% 0.21/0.57    $false | ~spl6_3),
% 0.21/0.57    inference(resolution,[],[f700,f96])).
% 0.21/0.57  fof(f700,plain,(
% 0.21/0.57    ( ! [X21] : (~sP1(sK2,sK2,sK2,X21)) ) | ~spl6_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f699,f608])).
% 0.21/0.57  fof(f608,plain,(
% 0.21/0.57    ( ! [X1] : (~sP1(sK2,sK2,sK2,X1) | ~r1_tarski(X1,sK3)) ) | ~spl6_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f607])).
% 0.21/0.57  fof(f607,plain,(
% 0.21/0.57    spl6_3 <=> ! [X1] : (~sP1(sK2,sK2,sK2,X1) | ~r1_tarski(X1,sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.57  fof(f699,plain,(
% 0.21/0.57    ( ! [X21] : (r1_tarski(X21,sK3) | ~sP1(sK2,sK2,sK2,X21)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f687,f106])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.21/0.57    inference(superposition,[],[f54,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.57  fof(f687,plain,(
% 0.21/0.57    ( ! [X21] : (~r1_tarski(k3_xboole_0(X21,sK3),sK3) | r1_tarski(X21,sK3) | ~sP1(sK2,sK2,sK2,X21)) )),
% 0.21/0.57    inference(superposition,[],[f406,f641])).
% 0.21/0.57  fof(f641,plain,(
% 0.21/0.57    ( ! [X10] : (k3_xboole_0(X10,sK3) = k5_xboole_0(X10,sK3) | ~sP1(sK2,sK2,sK2,X10)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f593,f50])).
% 0.21/0.57  fof(f593,plain,(
% 0.21/0.57    ( ! [X10] : (k5_xboole_0(X10,sK3) = k5_xboole_0(k3_xboole_0(X10,sK3),k1_xboole_0) | ~sP1(sK2,sK2,sK2,X10)) )),
% 0.21/0.57    inference(superposition,[],[f247,f570])).
% 0.21/0.57  fof(f247,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.57    inference(forward_demodulation,[],[f229,f116])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.57    inference(superposition,[],[f56,f50])).
% 0.21/0.57  fof(f229,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(superposition,[],[f66,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.57  fof(f406,plain,(
% 0.21/0.57    ( ! [X8,X7] : (~r1_tarski(k5_xboole_0(X8,X7),X7) | r1_tarski(X8,X7)) )),
% 0.21/0.57    inference(superposition,[],[f194,f251])).
% 0.21/0.57  fof(f251,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.21/0.57    inference(superposition,[],[f247,f56])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    ( ! [X19,X18] : (r1_tarski(k5_xboole_0(X19,X18),X19) | ~r1_tarski(X18,X19)) )),
% 0.21/0.57    inference(superposition,[],[f139,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)) )),
% 0.21/0.57    inference(superposition,[],[f89,f55])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f53,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.57  fof(f613,plain,(
% 0.21/0.57    spl6_3 | spl6_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f605,f610,f607])).
% 0.21/0.57  fof(f605,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = sK3 | ~sP1(sK2,sK2,sK2,X1) | ~r1_tarski(X1,sK3)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f576,f247])).
% 0.21/0.57  fof(f576,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X1,sK3)) | ~sP1(sK2,sK2,sK2,X1) | ~r1_tarski(X1,sK3)) )),
% 0.21/0.57    inference(superposition,[],[f570,f64])).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    spl6_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f171,f168])).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    ( ! [X9] : (~r2_hidden(X9,k1_xboole_0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f163,f133])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f124,f50])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.57    inference(superposition,[],[f57,f48])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    ( ! [X8,X9] : (~r2_hidden(X9,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X8)) )),
% 0.21/0.57    inference(superposition,[],[f63,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(resolution,[],[f52,f54])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (21038)------------------------------
% 0.21/0.57  % (21038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21038)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (21038)Memory used [KB]: 6652
% 0.21/0.57  % (21038)Time elapsed: 0.160 s
% 0.21/0.57  % (21038)------------------------------
% 0.21/0.57  % (21038)------------------------------
% 0.21/0.57  % (21010)Success in time 0.215 s
%------------------------------------------------------------------------------
