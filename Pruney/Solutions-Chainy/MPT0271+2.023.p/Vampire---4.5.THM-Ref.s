%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:09 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 213 expanded)
%              Number of leaves         :   19 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  328 ( 540 expanded)
%              Number of equality atoms :  149 ( 274 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f216,f219,f233,f467])).

fof(f467,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f262,f211,f103,f451])).

fof(f451,plain,
    ( ! [X16] :
        ( ~ r2_hidden(X16,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X16,sK1)
        | r2_hidden(X16,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f398,f214])).

fof(f214,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f398,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f397,f133])).

fof(f133,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f120,f110])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f60,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f120,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f59,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f397,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f105,f59])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f103,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f211,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f262,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(condensation,[],[f261])).

fof(f261,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X5,X4) ) ),
    inference(forward_demodulation,[],[f259,f65])).

fof(f259,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k5_xboole_0(X4,X4))
      | ~ r2_hidden(X5,X4) ) ),
    inference(condensation,[],[f254])).

fof(f254,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k5_xboole_0(X4,X4))
      | ~ r2_hidden(X5,X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(superposition,[],[f245,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f245,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(forward_demodulation,[],[f244,f133])).

fof(f244,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(forward_demodulation,[],[f106,f59])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f233,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f210,f230])).

fof(f230,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(trivial_inequality_removal,[],[f229])).

fof(f229,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f228,f65])).

fof(f228,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(superposition,[],[f215,f96])).

fof(f215,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f213])).

fof(f210,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f209])).

fof(f219,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f218,f213,f209])).

fof(f218,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f217,f133])).

fof(f217,plain,
    ( k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f81,f59])).

fof(f81,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f42,f75,f78])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f216,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f207,f213,f209])).

fof(f207,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f206,f133])).

fof(f206,plain,
    ( k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f80,f59])).

fof(f80,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f75,f78])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24472)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (24470)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24473)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (24489)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (24469)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (24480)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (24482)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (24476)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (24477)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (24478)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (24497)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (24471)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (24493)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (24498)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24498)Refutation not found, incomplete strategy% (24498)------------------------------
% 0.21/0.54  % (24498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24498)Memory used [KB]: 1663
% 0.21/0.54  % (24498)Time elapsed: 0.118 s
% 0.21/0.54  % (24498)------------------------------
% 0.21/0.54  % (24498)------------------------------
% 0.21/0.54  % (24484)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (24474)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24494)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (24495)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24492)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (24491)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (24488)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (24485)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (24485)Refutation not found, incomplete strategy% (24485)------------------------------
% 0.21/0.55  % (24485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24485)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24485)Memory used [KB]: 10618
% 0.21/0.55  % (24485)Time elapsed: 0.125 s
% 0.21/0.55  % (24485)------------------------------
% 0.21/0.55  % (24485)------------------------------
% 0.21/0.55  % (24483)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.55  % (24487)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.56  % (24486)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.56  % (24475)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.56  % (24496)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.56  % (24468)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.56  % (24479)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.57  % (24490)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.57  % (24492)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f468,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(avatar_sat_refutation,[],[f216,f219,f233,f467])).
% 1.46/0.57  fof(f467,plain,(
% 1.46/0.57    spl4_1 | ~spl4_2),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f461])).
% 1.46/0.57  fof(f461,plain,(
% 1.46/0.57    $false | (spl4_1 | ~spl4_2)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f262,f211,f103,f451])).
% 1.46/0.57  fof(f451,plain,(
% 1.46/0.57    ( ! [X16] : (~r2_hidden(X16,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X16,sK1) | r2_hidden(X16,k1_xboole_0)) ) | ~spl4_2),
% 1.46/0.57    inference(superposition,[],[f398,f214])).
% 1.46/0.57  fof(f214,plain,(
% 1.46/0.57    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | ~spl4_2),
% 1.46/0.57    inference(avatar_component_clause,[],[f213])).
% 1.46/0.57  fof(f213,plain,(
% 1.46/0.57    spl4_2 <=> k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.46/0.57  fof(f398,plain,(
% 1.46/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f397,f133])).
% 1.46/0.57  fof(f133,plain,(
% 1.46/0.57    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.46/0.57    inference(forward_demodulation,[],[f120,f110])).
% 1.46/0.57  fof(f110,plain,(
% 1.46/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.46/0.57    inference(superposition,[],[f60,f64])).
% 1.46/0.57  fof(f64,plain,(
% 1.46/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.46/0.57    inference(cnf_transformation,[],[f6])).
% 1.46/0.57  fof(f6,axiom,(
% 1.46/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.46/0.57  fof(f60,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.46/0.57  fof(f120,plain,(
% 1.46/0.57    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.46/0.57    inference(superposition,[],[f59,f65])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,axiom,(
% 1.46/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.46/0.57  fof(f59,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.46/0.57  fof(f397,plain,(
% 1.46/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f105,f59])).
% 1.46/0.57  fof(f105,plain,(
% 1.46/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.46/0.57    inference(equality_resolution,[],[f93])).
% 1.46/0.57  fof(f93,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 1.46/0.57    inference(definition_unfolding,[],[f54,f75])).
% 1.46/0.57  fof(f75,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.46/0.57    inference(definition_unfolding,[],[f62,f69])).
% 1.46/0.57  fof(f69,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,axiom,(
% 1.46/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.46/0.57  fof(f62,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.46/0.57  fof(f54,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.46/0.57    inference(cnf_transformation,[],[f39])).
% 1.46/0.57  fof(f39,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.46/0.57    inference(rectify,[],[f36])).
% 1.46/0.57  fof(f36,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.46/0.57    inference(flattening,[],[f35])).
% 1.46/0.57  fof(f35,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.46/0.57    inference(nnf_transformation,[],[f2])).
% 1.46/0.57  fof(f2,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.46/0.57  fof(f103,plain,(
% 1.46/0.57    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 1.46/0.57    inference(equality_resolution,[],[f102])).
% 1.46/0.57  fof(f102,plain,(
% 1.46/0.57    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 1.46/0.57    inference(equality_resolution,[],[f88])).
% 1.46/0.57  fof(f88,plain,(
% 1.46/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.46/0.57    inference(definition_unfolding,[],[f45,f76])).
% 1.46/0.57  fof(f76,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f66,f71])).
% 1.46/0.57  fof(f71,plain,(
% 1.46/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f15])).
% 1.46/0.57  fof(f15,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.46/0.57  fof(f66,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.46/0.57  fof(f45,plain,(
% 1.46/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.46/0.57    inference(cnf_transformation,[],[f34])).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.57    inference(rectify,[],[f31])).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.57    inference(flattening,[],[f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.57    inference(nnf_transformation,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.46/0.57    inference(ennf_transformation,[],[f11])).
% 1.46/0.57  fof(f11,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.46/0.57  fof(f211,plain,(
% 1.46/0.57    ~r2_hidden(sK0,sK1) | spl4_1),
% 1.46/0.57    inference(avatar_component_clause,[],[f209])).
% 1.46/0.57  fof(f209,plain,(
% 1.46/0.57    spl4_1 <=> r2_hidden(sK0,sK1)),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.46/0.57  fof(f262,plain,(
% 1.46/0.57    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 1.46/0.57    inference(condensation,[],[f261])).
% 1.46/0.57  fof(f261,plain,(
% 1.46/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,X4)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f259,f65])).
% 1.46/0.57  fof(f259,plain,(
% 1.46/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k5_xboole_0(X4,X4)) | ~r2_hidden(X5,X4)) )),
% 1.46/0.57    inference(condensation,[],[f254])).
% 1.46/0.57  fof(f254,plain,(
% 1.46/0.57    ( ! [X4,X5,X3] : (~r2_hidden(X5,k5_xboole_0(X4,X4)) | ~r2_hidden(X5,X4) | ~r2_hidden(X3,X4)) )),
% 1.46/0.57    inference(superposition,[],[f245,f96])).
% 1.46/0.57  fof(f96,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f58,f78])).
% 1.46/0.57  fof(f78,plain,(
% 1.46/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f63,f77])).
% 1.46/0.57  fof(f77,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f67,f76])).
% 1.46/0.57  fof(f67,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f13,axiom,(
% 1.46/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.46/0.57  fof(f63,plain,(
% 1.46/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f12])).
% 1.46/0.57  fof(f12,axiom,(
% 1.46/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.46/0.57  fof(f58,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f25])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f19])).
% 1.46/0.57  fof(f19,axiom,(
% 1.46/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.46/0.57  fof(f245,plain,(
% 1.46/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X1,k2_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f244,f133])).
% 1.46/0.57  fof(f244,plain,(
% 1.46/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))) | ~r2_hidden(X4,X1)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f106,f59])).
% 1.46/0.57  fof(f106,plain,(
% 1.46/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 1.46/0.57    inference(equality_resolution,[],[f94])).
% 1.46/0.57  fof(f94,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 1.46/0.57    inference(definition_unfolding,[],[f53,f75])).
% 1.46/0.57  fof(f53,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.46/0.57    inference(cnf_transformation,[],[f39])).
% 1.46/0.57  fof(f233,plain,(
% 1.46/0.57    ~spl4_1 | spl4_2),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f231])).
% 1.46/0.57  fof(f231,plain,(
% 1.46/0.57    $false | (~spl4_1 | spl4_2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f210,f230])).
% 1.46/0.57  fof(f230,plain,(
% 1.46/0.57    ~r2_hidden(sK0,sK1) | spl4_2),
% 1.46/0.57    inference(trivial_inequality_removal,[],[f229])).
% 1.46/0.57  fof(f229,plain,(
% 1.46/0.57    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,sK1) | spl4_2),
% 1.46/0.57    inference(forward_demodulation,[],[f228,f65])).
% 1.46/0.57  fof(f228,plain,(
% 1.46/0.57    k1_xboole_0 != k5_xboole_0(sK1,sK1) | ~r2_hidden(sK0,sK1) | spl4_2),
% 1.46/0.57    inference(superposition,[],[f215,f96])).
% 1.46/0.57  fof(f215,plain,(
% 1.46/0.57    k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_2),
% 1.46/0.57    inference(avatar_component_clause,[],[f213])).
% 1.46/0.57  fof(f210,plain,(
% 1.46/0.57    r2_hidden(sK0,sK1) | ~spl4_1),
% 1.46/0.57    inference(avatar_component_clause,[],[f209])).
% 1.46/0.57  fof(f219,plain,(
% 1.46/0.57    spl4_1 | spl4_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f218,f213,f209])).
% 1.46/0.57  fof(f218,plain,(
% 1.46/0.57    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | r2_hidden(sK0,sK1)),
% 1.46/0.57    inference(forward_demodulation,[],[f217,f133])).
% 1.46/0.57  fof(f217,plain,(
% 1.46/0.57    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))) | r2_hidden(sK0,sK1)),
% 1.46/0.57    inference(forward_demodulation,[],[f81,f59])).
% 1.46/0.57  fof(f81,plain,(
% 1.46/0.57    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.46/0.57    inference(definition_unfolding,[],[f42,f75,f78])).
% 1.46/0.57  fof(f42,plain,(
% 1.46/0.57    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f29])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.46/0.57    inference(nnf_transformation,[],[f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f22])).
% 1.46/0.57  fof(f22,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.46/0.57    inference(negated_conjecture,[],[f21])).
% 1.46/0.57  fof(f21,conjecture,(
% 1.46/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.46/0.57  fof(f216,plain,(
% 1.46/0.57    ~spl4_1 | ~spl4_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f207,f213,f209])).
% 1.46/0.57  fof(f207,plain,(
% 1.46/0.57    k1_xboole_0 != k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(sK0,sK1)),
% 1.46/0.57    inference(forward_demodulation,[],[f206,f133])).
% 1.46/0.57  fof(f206,plain,(
% 1.46/0.57    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))) | ~r2_hidden(sK0,sK1)),
% 1.46/0.57    inference(forward_demodulation,[],[f80,f59])).
% 1.46/0.57  fof(f80,plain,(
% 1.46/0.57    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.46/0.57    inference(definition_unfolding,[],[f43,f75,f78])).
% 1.46/0.57  fof(f43,plain,(
% 1.46/0.57    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f29])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (24492)------------------------------
% 1.46/0.57  % (24492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (24492)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (24492)Memory used [KB]: 11129
% 1.46/0.57  % (24492)Time elapsed: 0.126 s
% 1.46/0.57  % (24492)------------------------------
% 1.46/0.57  % (24492)------------------------------
% 1.46/0.58  % (24464)Success in time 0.208 s
%------------------------------------------------------------------------------
