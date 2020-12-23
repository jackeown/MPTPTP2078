%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:28 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 462 expanded)
%              Number of leaves         :   39 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  484 (1071 expanded)
%              Number of equality atoms :  175 ( 535 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f137,f141,f145,f200,f210,f214,f216,f222,f295,f301,f306,f349,f351])).

fof(f351,plain,
    ( ~ spl4_17
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f340,f290,f343])).

fof(f343,plain,
    ( spl4_17
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f290,plain,
    ( spl4_13
  <=> k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f340,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_13 ),
    inference(trivial_inequality_removal,[],[f317])).

fof(f317,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_13 ),
    inference(superposition,[],[f230,f291])).

fof(f291,plain,
    ( k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f290])).

fof(f230,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(inner_rewriting,[],[f229])).

fof(f229,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ) ),
    inference(forward_demodulation,[],[f228,f166])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f165,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f165,plain,(
    ! [X0] : v1_xboole_0(k5_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f161,f164])).

fof(f164,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f99,f97])).

fof(f97,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f93])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f60,f94])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f93])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f161,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_xboole_0(X0,X0),X0)
      | v1_xboole_0(k5_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f160,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f160,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f98,f97])).

fof(f98,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f59,f94])).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f228,plain,(
    ! [X0] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f102,f97])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1)))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f69,f94,f95])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f92])).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f349,plain,
    ( spl4_17
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f316,f290,f343])).

fof(f316,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_13 ),
    inference(superposition,[],[f120,f291])).

fof(f120,plain,(
    ! [X2,X0,X7,X3,X1] : r2_hidden(X7,k4_enumset1(X0,X0,X1,X2,X3,X7)) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X7) != X5 ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f83,f77])).

fof(f83,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
              & sK3(X0,X1,X2,X3,X4,X5) != X3
              & sK3(X0,X1,X2,X3,X4,X5) != X2
              & sK3(X0,X1,X2,X3,X4,X5) != X1
              & sK3(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK3(X0,X1,X2,X3,X4,X5) = X4
            | sK3(X0,X1,X2,X3,X4,X5) = X3
            | sK3(X0,X1,X2,X3,X4,X5) = X2
            | sK3(X0,X1,X2,X3,X4,X5) = X1
            | sK3(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
            & sK3(X0,X1,X2,X3,X4,X5) != X3
            & sK3(X0,X1,X2,X3,X4,X5) != X2
            & sK3(X0,X1,X2,X3,X4,X5) != X1
            & sK3(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK3(X0,X1,X2,X3,X4,X5) = X4
          | sK3(X0,X1,X2,X3,X4,X5) = X3
          | sK3(X0,X1,X2,X3,X4,X5) = X2
          | sK3(X0,X1,X2,X3,X4,X5) = X1
          | sK3(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f306,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f300,f120])).

fof(f300,plain,
    ( ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_15
  <=> r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f301,plain,
    ( ~ spl4_15
    | spl4_14 ),
    inference(avatar_split_clause,[],[f297,f293,f299])).

fof(f293,plain,
    ( spl4_14
  <=> r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f297,plain,
    ( ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl4_14 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl4_14 ),
    inference(resolution,[],[f294,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f75,f92])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f294,plain,
    ( ~ r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f293])).

fof(f295,plain,
    ( spl4_13
    | ~ spl4_14
    | spl4_10 ),
    inference(avatar_split_clause,[],[f285,f220,f293,f290])).

fof(f220,plain,
    ( spl4_10
  <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f285,plain,
    ( ~ r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | spl4_10 ),
    inference(resolution,[],[f282,f221])).

fof(f221,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f220])).

fof(f282,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f254,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f254,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(superposition,[],[f251,f97])).

fof(f251,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f232,f97])).

fof(f232,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_setfam_1(k1_setfam_1(k4_enumset1(X4,X4,X4,X4,X4,X5))),k1_zfmisc_1(k1_setfam_1(X3)))
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,X5)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f189,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))),k1_setfam_1(X0))
      | ~ r1_tarski(X0,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f93])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f222,plain,
    ( ~ spl4_8
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | spl4_7 ),
    inference(avatar_split_clause,[],[f217,f198,f220,f143,f135,f203])).

fof(f203,plain,
    ( spl4_8
  <=> v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f135,plain,
    ( spl4_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f143,plain,
    ( spl4_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f198,plain,
    ( spl4_7
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f217,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl4_7 ),
    inference(resolution,[],[f199,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f199,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f198])).

fof(f216,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f209,f100])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f61,f93])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f209,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_9
  <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f214,plain,
    ( ~ spl4_3
    | spl4_8 ),
    inference(avatar_split_clause,[],[f212,f203,f139])).

fof(f139,plain,
    ( spl4_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f212,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_8 ),
    inference(resolution,[],[f211,f151])).

fof(f151,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f100,f68])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_8 ),
    inference(resolution,[],[f204,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f204,plain,
    ( ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( ~ spl4_8
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9
    | spl4_6 ),
    inference(avatar_split_clause,[],[f201,f195,f208,f143,f139,f203])).

fof(f195,plain,
    ( spl4_6
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f201,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl4_6 ),
    inference(resolution,[],[f196,f56])).

fof(f196,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f195])).

fof(f200,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f191,f131,f198,f195])).

fof(f131,plain,
    ( spl4_1
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f191,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f103,f132])).

fof(f132,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f145,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f50,f143])).

fof(f50,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f141,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f51,f139])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f137,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f52,f135])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f133,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f96,f131])).

fof(f96,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f53,f93,f93])).

fof(f53,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (21908)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (21902)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (21913)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (21908)Refutation not found, incomplete strategy% (21908)------------------------------
% 0.21/0.53  % (21908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21908)Memory used [KB]: 10618
% 0.21/0.53  % (21908)Time elapsed: 0.109 s
% 0.21/0.53  % (21908)------------------------------
% 0.21/0.53  % (21908)------------------------------
% 0.21/0.53  % (21913)Refutation not found, incomplete strategy% (21913)------------------------------
% 0.21/0.53  % (21913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21897)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (21913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21913)Memory used [KB]: 10746
% 0.21/0.53  % (21913)Time elapsed: 0.007 s
% 0.21/0.53  % (21913)------------------------------
% 0.21/0.53  % (21913)------------------------------
% 0.21/0.54  % (21891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21896)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (21916)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21904)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (21899)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21899)Refutation not found, incomplete strategy% (21899)------------------------------
% 0.21/0.55  % (21899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21899)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21899)Memory used [KB]: 10746
% 0.21/0.55  % (21899)Time elapsed: 0.144 s
% 0.21/0.55  % (21899)------------------------------
% 0.21/0.55  % (21899)------------------------------
% 0.21/0.56  % (21895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (21895)Refutation not found, incomplete strategy% (21895)------------------------------
% 0.21/0.56  % (21895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21895)Memory used [KB]: 6268
% 0.21/0.56  % (21895)Time elapsed: 0.127 s
% 0.21/0.56  % (21895)------------------------------
% 0.21/0.56  % (21895)------------------------------
% 0.21/0.57  % (21912)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (21893)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (21912)Refutation not found, incomplete strategy% (21912)------------------------------
% 0.21/0.57  % (21912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21912)Memory used [KB]: 1791
% 0.21/0.57  % (21912)Time elapsed: 0.155 s
% 0.21/0.57  % (21912)------------------------------
% 0.21/0.57  % (21912)------------------------------
% 0.21/0.57  % (21905)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (21893)Refutation not found, incomplete strategy% (21893)------------------------------
% 0.21/0.57  % (21893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21893)Memory used [KB]: 10746
% 0.21/0.57  % (21893)Time elapsed: 0.156 s
% 0.21/0.57  % (21893)------------------------------
% 0.21/0.57  % (21893)------------------------------
% 0.21/0.57  % (21916)Refutation not found, incomplete strategy% (21916)------------------------------
% 0.21/0.57  % (21916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21909)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (21916)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21916)Memory used [KB]: 6652
% 0.21/0.57  % (21916)Time elapsed: 0.142 s
% 0.21/0.57  % (21916)------------------------------
% 0.21/0.57  % (21916)------------------------------
% 0.21/0.57  % (21918)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.58  % (21920)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (21900)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (21917)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (21919)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.58  % (21892)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (21910)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.59  % (21894)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.77/0.59  % (21898)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.77/0.59  % (21903)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.77/0.59  % (21911)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.77/0.59  % (21901)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.77/0.59  % (21901)Refutation not found, incomplete strategy% (21901)------------------------------
% 1.77/0.59  % (21901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (21901)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (21901)Memory used [KB]: 10618
% 1.77/0.59  % (21901)Time elapsed: 0.182 s
% 1.77/0.59  % (21901)------------------------------
% 1.77/0.59  % (21901)------------------------------
% 1.77/0.59  % (21911)Refutation not found, incomplete strategy% (21911)------------------------------
% 1.77/0.59  % (21911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (21911)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (21911)Memory used [KB]: 10746
% 1.77/0.59  % (21911)Time elapsed: 0.164 s
% 1.77/0.59  % (21911)------------------------------
% 1.77/0.59  % (21911)------------------------------
% 1.77/0.59  % (21915)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.77/0.60  % (21906)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.77/0.60  % (21914)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.91/0.60  % (21907)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.91/0.61  % (21910)Refutation found. Thanks to Tanya!
% 1.91/0.61  % SZS status Theorem for theBenchmark
% 1.91/0.61  % SZS output start Proof for theBenchmark
% 1.91/0.61  fof(f392,plain,(
% 1.91/0.61    $false),
% 1.91/0.61    inference(avatar_sat_refutation,[],[f133,f137,f141,f145,f200,f210,f214,f216,f222,f295,f301,f306,f349,f351])).
% 1.91/0.61  fof(f351,plain,(
% 1.91/0.61    ~spl4_17 | ~spl4_13),
% 1.91/0.61    inference(avatar_split_clause,[],[f340,f290,f343])).
% 1.91/0.61  fof(f343,plain,(
% 1.91/0.61    spl4_17 <=> r2_hidden(sK2,k1_xboole_0)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.91/0.61  fof(f290,plain,(
% 1.91/0.61    spl4_13 <=> k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.91/0.61  fof(f340,plain,(
% 1.91/0.61    ~r2_hidden(sK2,k1_xboole_0) | ~spl4_13),
% 1.91/0.61    inference(trivial_inequality_removal,[],[f317])).
% 1.91/0.61  fof(f317,plain,(
% 1.91/0.61    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK2,k1_xboole_0) | ~spl4_13),
% 1.91/0.61    inference(superposition,[],[f230,f291])).
% 1.91/0.61  fof(f291,plain,(
% 1.91/0.61    k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~spl4_13),
% 1.91/0.61    inference(avatar_component_clause,[],[f290])).
% 1.91/0.61  fof(f230,plain,(
% 1.91/0.61    ( ! [X0] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.91/0.61    inference(inner_rewriting,[],[f229])).
% 1.91/0.61  fof(f229,plain,(
% 1.91/0.61    ( ! [X0] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 1.91/0.61    inference(forward_demodulation,[],[f228,f166])).
% 1.91/0.61  fof(f166,plain,(
% 1.91/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.91/0.61    inference(resolution,[],[f165,f55])).
% 1.91/0.61  fof(f55,plain,(
% 1.91/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.91/0.61    inference(cnf_transformation,[],[f26])).
% 1.91/0.61  fof(f26,plain,(
% 1.91/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.91/0.61    inference(ennf_transformation,[],[f2])).
% 1.91/0.61  fof(f2,axiom,(
% 1.91/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.91/0.61  fof(f165,plain,(
% 1.91/0.61    ( ! [X0] : (v1_xboole_0(k5_xboole_0(X0,X0))) )),
% 1.91/0.61    inference(subsumption_resolution,[],[f161,f164])).
% 1.91/0.61  fof(f164,plain,(
% 1.91/0.61    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 1.91/0.61    inference(superposition,[],[f99,f97])).
% 1.91/0.61  fof(f97,plain,(
% 1.91/0.61    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.91/0.61    inference(definition_unfolding,[],[f58,f93])).
% 1.91/0.61  fof(f93,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.91/0.61    inference(definition_unfolding,[],[f62,f92])).
% 1.91/0.61  fof(f92,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f63,f91])).
% 1.91/0.61  fof(f91,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f71,f90])).
% 1.91/0.61  fof(f90,plain,(
% 1.91/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f76,f77])).
% 1.91/0.61  fof(f77,plain,(
% 1.91/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f13])).
% 1.91/0.61  fof(f13,axiom,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.91/0.61  fof(f76,plain,(
% 1.91/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f12])).
% 1.91/0.61  fof(f12,axiom,(
% 1.91/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.91/0.61  fof(f71,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f11])).
% 1.91/0.61  fof(f11,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.91/0.61  fof(f63,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f10])).
% 1.91/0.61  fof(f10,axiom,(
% 1.91/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.91/0.61  fof(f62,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f17])).
% 1.91/0.61  fof(f17,axiom,(
% 1.91/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.91/0.61  fof(f58,plain,(
% 1.91/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.91/0.61    inference(cnf_transformation,[],[f24])).
% 1.91/0.61  fof(f24,plain,(
% 1.91/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.91/0.61    inference(rectify,[],[f1])).
% 1.91/0.61  fof(f1,axiom,(
% 1.91/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.91/0.61  fof(f99,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f60,f94])).
% 1.91/0.61  fof(f94,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.91/0.61    inference(definition_unfolding,[],[f64,f93])).
% 1.91/0.61  fof(f64,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f3])).
% 1.91/0.61  fof(f3,axiom,(
% 1.91/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.91/0.61  fof(f60,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f6])).
% 1.91/0.61  fof(f6,axiom,(
% 1.91/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.91/0.61  fof(f161,plain,(
% 1.91/0.61    ( ! [X0] : (~r1_tarski(k5_xboole_0(X0,X0),X0) | v1_xboole_0(k5_xboole_0(X0,X0))) )),
% 1.91/0.61    inference(resolution,[],[f160,f65])).
% 1.91/0.61  fof(f65,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f31])).
% 1.91/0.61  fof(f31,plain,(
% 1.91/0.61    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.91/0.61    inference(flattening,[],[f30])).
% 1.91/0.61  fof(f30,plain,(
% 1.91/0.61    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.91/0.61    inference(ennf_transformation,[],[f7])).
% 1.91/0.61  fof(f7,axiom,(
% 1.91/0.61    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.91/0.61  fof(f160,plain,(
% 1.91/0.61    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 1.91/0.61    inference(superposition,[],[f98,f97])).
% 1.91/0.61  fof(f98,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f59,f94])).
% 1.91/0.61  fof(f59,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f8,axiom,(
% 1.91/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.91/0.61  fof(f228,plain,(
% 1.91/0.61    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 1.91/0.61    inference(superposition,[],[f102,f97])).
% 1.91/0.61  fof(f102,plain,(
% 1.91/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(X1,X1,X1,X1,X1,X1)))) != X0 | ~r2_hidden(X1,X0)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f69,f94,f95])).
% 1.91/0.61  fof(f95,plain,(
% 1.91/0.61    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f54,f92])).
% 1.91/0.61  fof(f54,plain,(
% 1.91/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f9])).
% 1.91/0.61  fof(f9,axiom,(
% 1.91/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.91/0.61  fof(f69,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.91/0.61    inference(cnf_transformation,[],[f42])).
% 1.91/0.61  fof(f42,plain,(
% 1.91/0.61    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.91/0.61    inference(nnf_transformation,[],[f15])).
% 1.91/0.61  fof(f15,axiom,(
% 1.91/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.91/0.61  fof(f349,plain,(
% 1.91/0.61    spl4_17 | ~spl4_13),
% 1.91/0.61    inference(avatar_split_clause,[],[f316,f290,f343])).
% 1.91/0.61  fof(f316,plain,(
% 1.91/0.61    r2_hidden(sK2,k1_xboole_0) | ~spl4_13),
% 1.91/0.61    inference(superposition,[],[f120,f291])).
% 1.91/0.61  fof(f120,plain,(
% 1.91/0.61    ( ! [X2,X0,X7,X3,X1] : (r2_hidden(X7,k4_enumset1(X0,X0,X1,X2,X3,X7))) )),
% 1.91/0.61    inference(equality_resolution,[],[f119])).
% 1.91/0.61  fof(f119,plain,(
% 1.91/0.61    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | k4_enumset1(X0,X0,X1,X2,X3,X7) != X5) )),
% 1.91/0.61    inference(equality_resolution,[],[f113])).
% 1.91/0.61  fof(f113,plain,(
% 1.91/0.61    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 1.91/0.61    inference(definition_unfolding,[],[f83,f77])).
% 1.91/0.61  fof(f83,plain,(
% 1.91/0.61    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.91/0.61    inference(cnf_transformation,[],[f49])).
% 1.91/0.61  fof(f49,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.91/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 1.91/0.61  fof(f48,plain,(
% 1.91/0.61    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 1.91/0.61    introduced(choice_axiom,[])).
% 1.91/0.61  fof(f47,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.91/0.61    inference(rectify,[],[f46])).
% 1.91/0.61  fof(f46,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.91/0.61    inference(flattening,[],[f45])).
% 1.91/0.61  fof(f45,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.91/0.61    inference(nnf_transformation,[],[f36])).
% 1.91/0.61  fof(f36,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.91/0.61    inference(ennf_transformation,[],[f16])).
% 1.91/0.61  fof(f16,axiom,(
% 1.91/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.91/0.61  fof(f306,plain,(
% 1.91/0.61    spl4_15),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f302])).
% 1.91/0.61  fof(f302,plain,(
% 1.91/0.61    $false | spl4_15),
% 1.91/0.61    inference(resolution,[],[f300,f120])).
% 1.91/0.61  fof(f300,plain,(
% 1.91/0.61    ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl4_15),
% 1.91/0.61    inference(avatar_component_clause,[],[f299])).
% 1.91/0.61  fof(f299,plain,(
% 1.91/0.61    spl4_15 <=> r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.91/0.61  fof(f301,plain,(
% 1.91/0.61    ~spl4_15 | spl4_14),
% 1.91/0.61    inference(avatar_split_clause,[],[f297,f293,f299])).
% 1.91/0.61  fof(f293,plain,(
% 1.91/0.61    spl4_14 <=> r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.91/0.61  fof(f297,plain,(
% 1.91/0.61    ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl4_14),
% 1.91/0.61    inference(duplicate_literal_removal,[],[f296])).
% 1.91/0.61  fof(f296,plain,(
% 1.91/0.61    ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl4_14),
% 1.91/0.61    inference(resolution,[],[f294,f104])).
% 1.91/0.61  fof(f104,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f75,f92])).
% 1.91/0.61  fof(f75,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f44,plain,(
% 1.91/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.91/0.61    inference(flattening,[],[f43])).
% 1.91/0.61  fof(f43,plain,(
% 1.91/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.91/0.61    inference(nnf_transformation,[],[f14])).
% 1.91/0.61  fof(f14,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.91/0.61  fof(f294,plain,(
% 1.91/0.61    ~r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl4_14),
% 1.91/0.61    inference(avatar_component_clause,[],[f293])).
% 1.91/0.61  fof(f295,plain,(
% 1.91/0.61    spl4_13 | ~spl4_14 | spl4_10),
% 1.91/0.61    inference(avatar_split_clause,[],[f285,f220,f293,f290])).
% 1.91/0.61  fof(f220,plain,(
% 1.91/0.61    spl4_10 <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.91/0.61  fof(f285,plain,(
% 1.91/0.61    ~r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | spl4_10),
% 1.91/0.61    inference(resolution,[],[f282,f221])).
% 1.91/0.61  fof(f221,plain,(
% 1.91/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | spl4_10),
% 1.91/0.61    inference(avatar_component_clause,[],[f220])).
% 1.91/0.61  fof(f282,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.91/0.61    inference(resolution,[],[f254,f67])).
% 1.91/0.61  fof(f67,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f41])).
% 1.91/0.61  fof(f41,plain,(
% 1.91/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.91/0.61    inference(nnf_transformation,[],[f18])).
% 1.91/0.61  fof(f18,axiom,(
% 1.91/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.91/0.61  fof(f254,plain,(
% 1.91/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)) )),
% 1.91/0.61    inference(superposition,[],[f251,f97])).
% 1.91/0.61  fof(f251,plain,(
% 1.91/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X0)) )),
% 1.91/0.61    inference(duplicate_literal_removal,[],[f249])).
% 1.91/0.61  fof(f249,plain,(
% 1.91/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X1,X0)) )),
% 1.91/0.61    inference(superposition,[],[f232,f97])).
% 1.91/0.61  fof(f232,plain,(
% 1.91/0.61    ( ! [X4,X5,X3] : (m1_subset_1(k1_setfam_1(k1_setfam_1(k4_enumset1(X4,X4,X4,X4,X4,X5))),k1_zfmisc_1(k1_setfam_1(X3))) | k1_xboole_0 = X3 | ~r1_tarski(X3,X5) | ~r1_tarski(X3,X4)) )),
% 1.91/0.61    inference(resolution,[],[f189,f68])).
% 1.91/0.61  fof(f68,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f41])).
% 1.91/0.61  fof(f189,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))),k1_setfam_1(X0)) | ~r1_tarski(X0,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.91/0.61    inference(resolution,[],[f103,f66])).
% 1.91/0.61  fof(f66,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f33])).
% 1.91/0.61  fof(f33,plain,(
% 1.91/0.61    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.91/0.61    inference(flattening,[],[f32])).
% 1.91/0.61  fof(f32,plain,(
% 1.91/0.61    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.91/0.61    inference(ennf_transformation,[],[f19])).
% 1.91/0.61  fof(f19,axiom,(
% 1.91/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.91/0.61  fof(f103,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f72,f93])).
% 1.91/0.61  fof(f72,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f35])).
% 1.91/0.61  fof(f35,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.91/0.61    inference(flattening,[],[f34])).
% 1.91/0.61  fof(f34,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.91/0.61    inference(ennf_transformation,[],[f5])).
% 1.91/0.61  fof(f5,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.91/0.61  fof(f222,plain,(
% 1.91/0.61    ~spl4_8 | ~spl4_2 | ~spl4_4 | ~spl4_10 | spl4_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f217,f198,f220,f143,f135,f203])).
% 1.91/0.61  fof(f203,plain,(
% 1.91/0.61    spl4_8 <=> v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.91/0.61  fof(f135,plain,(
% 1.91/0.61    spl4_2 <=> v1_relat_1(sK2)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.91/0.61  fof(f143,plain,(
% 1.91/0.61    spl4_4 <=> v1_relat_1(sK0)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.91/0.61  fof(f198,plain,(
% 1.91/0.61    spl4_7 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.91/0.61  fof(f217,plain,(
% 1.91/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl4_7),
% 1.91/0.61    inference(resolution,[],[f199,f56])).
% 1.91/0.61  fof(f56,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f28])).
% 1.91/0.61  fof(f28,plain,(
% 1.91/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.91/0.61    inference(flattening,[],[f27])).
% 1.91/0.61  fof(f27,plain,(
% 1.91/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.91/0.61    inference(ennf_transformation,[],[f21])).
% 1.91/0.61  fof(f21,axiom,(
% 1.91/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 1.91/0.61  fof(f199,plain,(
% 1.91/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl4_7),
% 1.91/0.61    inference(avatar_component_clause,[],[f198])).
% 1.91/0.61  fof(f216,plain,(
% 1.91/0.61    spl4_9),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f215])).
% 1.91/0.61  fof(f215,plain,(
% 1.91/0.61    $false | spl4_9),
% 1.91/0.61    inference(resolution,[],[f209,f100])).
% 1.91/0.61  fof(f100,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.91/0.61    inference(definition_unfolding,[],[f61,f93])).
% 1.91/0.61  fof(f61,plain,(
% 1.91/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f4])).
% 1.91/0.61  fof(f4,axiom,(
% 1.91/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.91/0.61  fof(f209,plain,(
% 1.91/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | spl4_9),
% 1.91/0.61    inference(avatar_component_clause,[],[f208])).
% 1.91/0.61  fof(f208,plain,(
% 1.91/0.61    spl4_9 <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.91/0.61  fof(f214,plain,(
% 1.91/0.61    ~spl4_3 | spl4_8),
% 1.91/0.61    inference(avatar_split_clause,[],[f212,f203,f139])).
% 1.91/0.61  fof(f139,plain,(
% 1.91/0.61    spl4_3 <=> v1_relat_1(sK1)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.91/0.61  fof(f212,plain,(
% 1.91/0.61    ~v1_relat_1(sK1) | spl4_8),
% 1.91/0.61    inference(resolution,[],[f211,f151])).
% 1.91/0.61  fof(f151,plain,(
% 1.91/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 1.91/0.61    inference(resolution,[],[f100,f68])).
% 1.91/0.61  fof(f211,plain,(
% 1.91/0.61    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_8),
% 1.91/0.61    inference(resolution,[],[f204,f57])).
% 1.91/0.61  fof(f57,plain,(
% 1.91/0.61    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f29])).
% 1.91/0.61  fof(f29,plain,(
% 1.91/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.91/0.61    inference(ennf_transformation,[],[f20])).
% 1.91/0.61  fof(f20,axiom,(
% 1.91/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.91/0.61  fof(f204,plain,(
% 1.91/0.61    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl4_8),
% 1.91/0.61    inference(avatar_component_clause,[],[f203])).
% 1.91/0.61  fof(f210,plain,(
% 1.91/0.61    ~spl4_8 | ~spl4_3 | ~spl4_4 | ~spl4_9 | spl4_6),
% 1.91/0.61    inference(avatar_split_clause,[],[f201,f195,f208,f143,f139,f203])).
% 1.91/0.61  fof(f195,plain,(
% 1.91/0.61    spl4_6 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.91/0.61  fof(f201,plain,(
% 1.91/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl4_6),
% 1.91/0.61    inference(resolution,[],[f196,f56])).
% 1.91/0.61  fof(f196,plain,(
% 1.91/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl4_6),
% 1.91/0.61    inference(avatar_component_clause,[],[f195])).
% 1.91/0.61  fof(f200,plain,(
% 1.91/0.61    ~spl4_6 | ~spl4_7 | spl4_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f191,f131,f198,f195])).
% 1.91/0.61  fof(f131,plain,(
% 1.91/0.61    spl4_1 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.91/0.61  fof(f191,plain,(
% 1.91/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl4_1),
% 1.91/0.61    inference(resolution,[],[f103,f132])).
% 1.91/0.61  fof(f132,plain,(
% 1.91/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) | spl4_1),
% 1.91/0.61    inference(avatar_component_clause,[],[f131])).
% 1.91/0.61  fof(f145,plain,(
% 1.91/0.61    spl4_4),
% 1.91/0.61    inference(avatar_split_clause,[],[f50,f143])).
% 1.91/0.61  fof(f50,plain,(
% 1.91/0.61    v1_relat_1(sK0)),
% 1.91/0.61    inference(cnf_transformation,[],[f40])).
% 1.91/0.61  fof(f40,plain,(
% 1.91/0.61    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.91/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f39,f38,f37])).
% 1.91/0.61  fof(f37,plain,(
% 1.91/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.91/0.61    introduced(choice_axiom,[])).
% 1.91/0.61  fof(f38,plain,(
% 1.91/0.61    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.91/0.61    introduced(choice_axiom,[])).
% 1.91/0.61  fof(f39,plain,(
% 1.91/0.61    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 1.91/0.61    introduced(choice_axiom,[])).
% 1.91/0.61  fof(f25,plain,(
% 1.91/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.91/0.61    inference(ennf_transformation,[],[f23])).
% 1.91/0.61  fof(f23,negated_conjecture,(
% 1.91/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.91/0.61    inference(negated_conjecture,[],[f22])).
% 1.91/0.61  fof(f22,conjecture,(
% 1.91/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 1.91/0.61  fof(f141,plain,(
% 1.91/0.61    spl4_3),
% 1.91/0.61    inference(avatar_split_clause,[],[f51,f139])).
% 1.91/0.61  fof(f51,plain,(
% 1.91/0.61    v1_relat_1(sK1)),
% 1.91/0.61    inference(cnf_transformation,[],[f40])).
% 1.91/0.61  fof(f137,plain,(
% 1.91/0.61    spl4_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f52,f135])).
% 1.91/0.61  fof(f52,plain,(
% 1.91/0.61    v1_relat_1(sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f40])).
% 1.91/0.61  fof(f133,plain,(
% 1.91/0.61    ~spl4_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f96,f131])).
% 1.91/0.61  fof(f96,plain,(
% 1.91/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.91/0.61    inference(definition_unfolding,[],[f53,f93,f93])).
% 1.91/0.61  fof(f53,plain,(
% 1.91/0.61    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.91/0.61    inference(cnf_transformation,[],[f40])).
% 1.91/0.61  % SZS output end Proof for theBenchmark
% 1.91/0.61  % (21910)------------------------------
% 1.91/0.61  % (21910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (21910)Termination reason: Refutation
% 1.91/0.61  
% 1.91/0.61  % (21910)Memory used [KB]: 11001
% 1.91/0.61  % (21910)Time elapsed: 0.187 s
% 1.91/0.61  % (21910)------------------------------
% 1.91/0.61  % (21910)------------------------------
% 1.91/0.61  % (21890)Success in time 0.242 s
%------------------------------------------------------------------------------
