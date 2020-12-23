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
% DateTime   : Thu Dec  3 12:32:37 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 211 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  244 ( 685 expanded)
%              Number of equality atoms :   41 ( 129 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f583,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f446,f582])).

fof(f582,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f570,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f570,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f348,f214])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)
      | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f213,f125])).

fof(f125,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f114,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f114,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f104,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f104,plain,(
    r1_tarski(k5_xboole_0(sK0,sK0),sK0) ),
    inference(superposition,[],[f48,f72])).

fof(f72,plain,(
    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f47,f37])).

fof(f47,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f213,plain,(
    ! [X0] :
      ( k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,sK0)
      | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) ) ),
    inference(forward_demodulation,[],[f212,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f212,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))
      | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) ) ),
    inference(forward_demodulation,[],[f192,f29])).

fof(f192,plain,(
    ! [X0] :
      ( k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
      | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) ) ),
    inference(superposition,[],[f107,f37])).

fof(f107,plain,(
    ! [X0] : k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f51,f72])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f40,f33,f33])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f348,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f64,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f446,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f439,f368])).

fof(f368,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK2)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f350,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f33])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f350,plain,
    ( r2_hidden(sK3(sK0,sK2),sK2)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f68,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f439,plain,
    ( r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f349,f343])).

fof(f343,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | r2_hidden(X4,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f118,f143])).

fof(f143,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f142,f120])).

fof(f120,plain,(
    ! [X6] :
      ( r2_hidden(X6,sK0)
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f113,f29])).

fof(f113,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k5_xboole_0(sK0,sK0))
      | r2_hidden(X6,sK0) ) ),
    inference(superposition,[],[f60,f72])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f142,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(forward_demodulation,[],[f136,f29])).

fof(f136,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k5_xboole_0(sK0,sK0))
      | ~ r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f59,f122])).

fof(f122,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f103,f37])).

fof(f103,plain,(
    r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f31,f72])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f118,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_xboole_0)
      | r2_hidden(X4,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
      | ~ r2_hidden(X4,sK0) ) ),
    inference(forward_demodulation,[],[f111,f29])).

fof(f111,plain,(
    ! [X4] :
      ( r2_hidden(X4,k5_xboole_0(sK0,sK0))
      | r2_hidden(X4,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
      | ~ r2_hidden(X4,sK0) ) ),
    inference(superposition,[],[f58,f72])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f33])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f349,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f28,f66,f62])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (12963)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (12969)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12968)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (12975)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12965)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (12966)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (12981)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.53  % (12967)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.53  % (12983)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.54  % (12964)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (12989)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (12990)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (12985)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.54  % (12971)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.54  % (12988)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.54  % (12977)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.55  % (12982)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.55  % (12973)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.55  % (12980)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (12986)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.55  % (12974)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.55  % (12978)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.55  % (12974)Refutation not found, incomplete strategy% (12974)------------------------------
% 1.50/0.55  % (12974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (12974)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (12974)Memory used [KB]: 10618
% 1.50/0.55  % (12974)Time elapsed: 0.153 s
% 1.50/0.55  % (12974)------------------------------
% 1.50/0.55  % (12974)------------------------------
% 1.50/0.55  % (12979)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.55  % (12970)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.55  % (12972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (12991)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.56  % (12987)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.56  % (12978)Refutation not found, incomplete strategy% (12978)------------------------------
% 1.50/0.56  % (12978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12978)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (12978)Memory used [KB]: 6140
% 1.50/0.57  % (12978)Time elapsed: 0.004 s
% 1.50/0.57  % (12978)------------------------------
% 1.50/0.57  % (12978)------------------------------
% 1.50/0.59  % (12989)Refutation found. Thanks to Tanya!
% 1.50/0.59  % SZS status Theorem for theBenchmark
% 1.50/0.59  % (12976)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.60  % SZS output start Proof for theBenchmark
% 1.50/0.60  fof(f583,plain,(
% 1.50/0.60    $false),
% 1.50/0.60    inference(avatar_sat_refutation,[],[f69,f446,f582])).
% 1.50/0.60  fof(f582,plain,(
% 1.50/0.60    spl5_1),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f581])).
% 1.50/0.60  fof(f581,plain,(
% 1.50/0.60    $false | spl5_1),
% 1.50/0.60    inference(subsumption_resolution,[],[f570,f48])).
% 1.50/0.60  fof(f48,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f30,f33])).
% 1.50/0.60  fof(f33,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f5])).
% 1.50/0.60  fof(f5,axiom,(
% 1.50/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.60  fof(f30,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f8])).
% 1.50/0.60  fof(f8,axiom,(
% 1.50/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.50/0.60  fof(f570,plain,(
% 1.50/0.60    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) | spl5_1),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f348,f214])).
% 1.50/0.60  fof(f214,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 1.50/0.60    inference(forward_demodulation,[],[f213,f125])).
% 1.50/0.60  fof(f125,plain,(
% 1.50/0.60    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f114,f37])).
% 1.50/0.60  fof(f37,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f16])).
% 1.50/0.60  fof(f16,plain,(
% 1.50/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.50/0.60    inference(ennf_transformation,[],[f7])).
% 1.50/0.60  fof(f7,axiom,(
% 1.50/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.50/0.60  fof(f114,plain,(
% 1.50/0.60    r1_tarski(k1_xboole_0,sK0)),
% 1.50/0.60    inference(forward_demodulation,[],[f104,f29])).
% 1.50/0.60  fof(f29,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f10])).
% 1.50/0.60  fof(f10,axiom,(
% 1.50/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.50/0.60  fof(f104,plain,(
% 1.50/0.60    r1_tarski(k5_xboole_0(sK0,sK0),sK0)),
% 1.50/0.60    inference(superposition,[],[f48,f72])).
% 1.50/0.60  fof(f72,plain,(
% 1.50/0.60    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f47,f37])).
% 1.50/0.60  fof(f47,plain,(
% 1.50/0.60    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.50/0.60    inference(definition_unfolding,[],[f27,f33])).
% 1.50/0.60  fof(f27,plain,(
% 1.50/0.60    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.50/0.60    inference(cnf_transformation,[],[f18])).
% 1.50/0.60  fof(f18,plain,(
% 1.50/0.60    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 1.50/0.60  fof(f17,plain,(
% 1.50/0.60    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f14,plain,(
% 1.50/0.60    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.50/0.60    inference(ennf_transformation,[],[f12])).
% 1.50/0.60  fof(f12,negated_conjecture,(
% 1.50/0.60    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.50/0.60    inference(negated_conjecture,[],[f11])).
% 1.50/0.60  fof(f11,conjecture,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.50/0.60  fof(f213,plain,(
% 1.50/0.60    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,sK0) | ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) )),
% 1.50/0.60    inference(forward_demodulation,[],[f212,f32])).
% 1.50/0.60  fof(f32,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f1])).
% 1.50/0.60  fof(f1,axiom,(
% 1.50/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.50/0.60  fof(f212,plain,(
% 1.50/0.60    ( ! [X0] : (k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) | ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) )),
% 1.50/0.60    inference(forward_demodulation,[],[f192,f29])).
% 1.50/0.60  fof(f192,plain,(
% 1.50/0.60    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) )),
% 1.50/0.60    inference(superposition,[],[f107,f37])).
% 1.50/0.60  fof(f107,plain,(
% 1.50/0.60    ( ! [X0] : (k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 1.50/0.60    inference(superposition,[],[f51,f72])).
% 1.50/0.60  fof(f51,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f40,f33,f33])).
% 1.50/0.60  fof(f40,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f9])).
% 1.50/0.60  fof(f9,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.50/0.60  fof(f348,plain,(
% 1.50/0.60    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl5_1),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f64,f50])).
% 1.50/0.60  fof(f50,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f38,f33])).
% 1.50/0.60  fof(f38,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f21])).
% 1.50/0.60  fof(f21,plain,(
% 1.50/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.50/0.60    inference(nnf_transformation,[],[f4])).
% 1.50/0.60  fof(f4,axiom,(
% 1.50/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.50/0.60  fof(f64,plain,(
% 1.50/0.60    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.50/0.60    inference(avatar_component_clause,[],[f62])).
% 1.50/0.60  fof(f62,plain,(
% 1.50/0.60    spl5_1 <=> r1_tarski(sK0,sK1)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.50/0.60  fof(f446,plain,(
% 1.50/0.60    spl5_2),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f445])).
% 1.50/0.60  fof(f445,plain,(
% 1.50/0.60    $false | spl5_2),
% 1.50/0.60    inference(subsumption_resolution,[],[f439,f368])).
% 1.50/0.60  fof(f368,plain,(
% 1.50/0.60    ( ! [X0] : (~r2_hidden(sK3(sK0,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) ) | spl5_2),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f350,f59])).
% 1.50/0.60  fof(f59,plain,(
% 1.50/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.50/0.60    inference(equality_resolution,[],[f56])).
% 1.50/0.60  fof(f56,plain,(
% 1.50/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.50/0.60    inference(definition_unfolding,[],[f42,f33])).
% 1.50/0.60  fof(f42,plain,(
% 1.50/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.50/0.60    inference(cnf_transformation,[],[f26])).
% 1.50/0.60  fof(f26,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.50/0.60  fof(f25,plain,(
% 1.50/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f24,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.50/0.60    inference(rectify,[],[f23])).
% 1.50/0.60  fof(f23,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.50/0.60    inference(flattening,[],[f22])).
% 1.50/0.60  fof(f22,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.50/0.60    inference(nnf_transformation,[],[f2])).
% 1.50/0.60  fof(f2,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.50/0.60  fof(f350,plain,(
% 1.50/0.60    r2_hidden(sK3(sK0,sK2),sK2) | spl5_2),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f68,f35])).
% 1.50/0.60  fof(f35,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f20])).
% 1.50/0.60  fof(f20,plain,(
% 1.50/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f19])).
% 1.50/0.60  fof(f19,plain,(
% 1.50/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f15,plain,(
% 1.50/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.50/0.60    inference(ennf_transformation,[],[f13])).
% 1.50/0.60  fof(f13,plain,(
% 1.50/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.60    inference(rectify,[],[f3])).
% 1.50/0.60  fof(f3,axiom,(
% 1.50/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.50/0.60  fof(f68,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK2) | spl5_2),
% 1.50/0.60    inference(avatar_component_clause,[],[f66])).
% 1.50/0.60  fof(f66,plain,(
% 1.50/0.60    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.50/0.61  fof(f439,plain,(
% 1.50/0.61    r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | spl5_2),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f349,f343])).
% 1.50/0.61  fof(f343,plain,(
% 1.50/0.61    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(X4,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) )),
% 1.50/0.61    inference(subsumption_resolution,[],[f118,f143])).
% 1.50/0.61  fof(f143,plain,(
% 1.50/0.61    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 1.50/0.61    inference(subsumption_resolution,[],[f142,f120])).
% 1.50/0.61  fof(f120,plain,(
% 1.50/0.61    ( ! [X6] : (r2_hidden(X6,sK0) | ~r2_hidden(X6,k1_xboole_0)) )),
% 1.50/0.61    inference(forward_demodulation,[],[f113,f29])).
% 1.50/0.61  fof(f113,plain,(
% 1.50/0.61    ( ! [X6] : (~r2_hidden(X6,k5_xboole_0(sK0,sK0)) | r2_hidden(X6,sK0)) )),
% 1.50/0.61    inference(superposition,[],[f60,f72])).
% 1.50/0.61  fof(f60,plain,(
% 1.50/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.50/0.61    inference(equality_resolution,[],[f57])).
% 1.50/0.61  fof(f57,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.50/0.61    inference(definition_unfolding,[],[f41,f33])).
% 1.50/0.61  fof(f41,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.50/0.61    inference(cnf_transformation,[],[f26])).
% 1.50/0.61  fof(f142,plain,(
% 1.50/0.61    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,sK0)) )),
% 1.50/0.61    inference(forward_demodulation,[],[f136,f29])).
% 1.50/0.61  fof(f136,plain,(
% 1.50/0.61    ( ! [X5] : (~r2_hidden(X5,k5_xboole_0(sK0,sK0)) | ~r2_hidden(X5,sK0)) )),
% 1.50/0.61    inference(superposition,[],[f59,f122])).
% 1.50/0.61  fof(f122,plain,(
% 1.50/0.61    sK0 = k3_xboole_0(sK0,sK0)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f103,f37])).
% 1.50/0.61  fof(f103,plain,(
% 1.50/0.61    r1_tarski(sK0,sK0)),
% 1.50/0.61    inference(superposition,[],[f31,f72])).
% 1.50/0.61  fof(f31,plain,(
% 1.50/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f6])).
% 1.50/0.61  fof(f6,axiom,(
% 1.50/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.50/0.61  fof(f118,plain,(
% 1.50/0.61    ( ! [X4] : (r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~r2_hidden(X4,sK0)) )),
% 1.50/0.61    inference(forward_demodulation,[],[f111,f29])).
% 1.50/0.61  fof(f111,plain,(
% 1.50/0.61    ( ! [X4] : (r2_hidden(X4,k5_xboole_0(sK0,sK0)) | r2_hidden(X4,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~r2_hidden(X4,sK0)) )),
% 1.50/0.61    inference(superposition,[],[f58,f72])).
% 1.50/0.61  fof(f58,plain,(
% 1.50/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.50/0.61    inference(equality_resolution,[],[f55])).
% 1.50/0.61  fof(f55,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.50/0.61    inference(definition_unfolding,[],[f43,f33])).
% 1.50/0.61  fof(f43,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.50/0.61    inference(cnf_transformation,[],[f26])).
% 1.50/0.61  fof(f349,plain,(
% 1.50/0.61    r2_hidden(sK3(sK0,sK2),sK0) | spl5_2),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f68,f34])).
% 1.50/0.61  fof(f34,plain,(
% 1.50/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f20])).
% 1.50/0.61  fof(f69,plain,(
% 1.50/0.61    ~spl5_1 | ~spl5_2),
% 1.50/0.61    inference(avatar_split_clause,[],[f28,f66,f62])).
% 1.50/0.61  fof(f28,plain,(
% 1.50/0.61    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.50/0.61    inference(cnf_transformation,[],[f18])).
% 1.50/0.61  % SZS output end Proof for theBenchmark
% 1.50/0.61  % (12989)------------------------------
% 1.50/0.61  % (12989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (12989)Termination reason: Refutation
% 1.50/0.61  
% 1.50/0.61  % (12989)Memory used [KB]: 11001
% 1.50/0.61  % (12989)Time elapsed: 0.176 s
% 1.50/0.61  % (12989)------------------------------
% 1.50/0.61  % (12989)------------------------------
% 1.50/0.61  % (12962)Success in time 0.247 s
%------------------------------------------------------------------------------
