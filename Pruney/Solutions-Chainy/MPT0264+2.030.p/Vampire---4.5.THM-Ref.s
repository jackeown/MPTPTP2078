%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:25 EST 2020

% Result     : Theorem 8.58s
% Output     : Refutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 673 expanded)
%              Number of leaves         :   36 ( 236 expanded)
%              Depth                    :   15
%              Number of atoms          :  356 (1020 expanded)
%              Number of equality atoms :  206 ( 808 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f133,f138,f497,f515,f1787,f1797,f3895,f3942,f4733,f5154,f5280])).

fof(f5280,plain,
    ( spl5_1
    | ~ spl5_114 ),
    inference(avatar_contradiction_clause,[],[f5279])).

fof(f5279,plain,
    ( $false
    | spl5_1
    | ~ spl5_114 ),
    inference(subsumption_resolution,[],[f5270,f127])).

fof(f127,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f5270,plain,
    ( sK0 = sK1
    | ~ spl5_114 ),
    inference(duplicate_literal_removal,[],[f5266])).

fof(f5266,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl5_114 ),
    inference(resolution,[],[f5153,f279])).

fof(f279,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X2,X2,X2,X2,X2,X1,X0,X0))
      | X1 = X3
      | X0 = X3
      | X2 = X3 ) ),
    inference(superposition,[],[f123,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f67,f84,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f123,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f5153,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f5151])).

fof(f5151,plain,
    ( spl5_114
  <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f5154,plain,
    ( spl5_114
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f5107,f1784,f5151])).

fof(f1784,plain,
    ( spl5_25
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f5107,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_25 ),
    inference(superposition,[],[f118,f1786])).

fof(f1786,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f1784])).

fof(f118,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4733,plain,
    ( spl5_26
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f4690,f3547,f1794])).

fof(f1794,plain,
    ( spl5_26
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f3547,plain,
    ( spl5_39
  <=> sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f4690,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f4677,f296])).

fof(f296,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(forward_demodulation,[],[f152,f229])).

fof(f229,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f228,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f228,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f93,f92])).

fof(f92,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f89])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f86])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f152,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f139,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f139,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f63,f48])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f4677,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2))
    | r2_hidden(sK0,sK2)
    | ~ spl5_39 ),
    inference(superposition,[],[f474,f3549])).

fof(f3549,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f3547])).

fof(f474,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))
      | r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f96,f63])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f57,f89,f88,f89])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f3942,plain,
    ( spl5_39
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f3899,f3892,f3547])).

fof(f3892,plain,
    ( spl5_59
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f3899,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_59 ),
    inference(superposition,[],[f297,f3894])).

fof(f3894,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f3892])).

fof(f297,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X0 ),
    inference(forward_demodulation,[],[f94,f63])).

fof(f94,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f52,f87,f88])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f3895,plain,
    ( spl5_59
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f3890,f511,f3892])).

fof(f511,plain,
    ( spl5_5
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f3890,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f513,f599])).

fof(f599,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X5) ),
    inference(superposition,[],[f113,f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f81,f87,f83,f85])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f79,f82,f87,f83,f89])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f513,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f511])).

fof(f1797,plain,
    ( ~ spl5_26
    | ~ spl5_2
    | spl5_24 ),
    inference(avatar_split_clause,[],[f1792,f1780,f130,f1794])).

fof(f130,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1780,plain,
    ( spl5_24
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1792,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_2
    | spl5_24 ),
    inference(subsumption_resolution,[],[f1789,f132])).

fof(f132,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1789,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl5_24 ),
    inference(resolution,[],[f1782,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f66,f86])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1782,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1787,plain,
    ( ~ spl5_24
    | spl5_25
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1778,f494,f1784,f1780])).

fof(f494,plain,
    ( spl5_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1778,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1777,f229])).

fof(f1777,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1776,f139])).

fof(f1776,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1770,f51])).

fof(f1770,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_4 ),
    inference(superposition,[],[f496,f262])).

fof(f262,plain,(
    ! [X8,X7] :
      ( k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X7,X7,X7)) = X8
      | ~ r1_tarski(X7,X8) ) ),
    inference(superposition,[],[f95,f104])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f496,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f494])).

fof(f515,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f500,f494,f511])).

fof(f500,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | ~ spl5_4 ),
    inference(superposition,[],[f63,f496])).

fof(f497,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f492,f135,f494])).

fof(f135,plain,
    ( spl5_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f492,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f491,f51])).

fof(f491,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f137,f104])).

fof(f137,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f138,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f91,f135])).

fof(f91,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) ),
    inference(definition_unfolding,[],[f44,f89,f88,f86])).

fof(f44,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != sK1
    & r2_hidden(sK1,sK2)
    & k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) )
   => ( sK0 != sK1
      & r2_hidden(sK1,sK2)
      & k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f133,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f45,f130])).

fof(f45,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f128,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f46,f125])).

fof(f46,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (23850)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (23842)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (23827)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23825)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (23829)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (23823)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (23851)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23832)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (23826)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (23824)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (23822)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (23831)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (23852)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (23852)Refutation not found, incomplete strategy% (23852)------------------------------
% 0.21/0.55  % (23852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23852)Memory used [KB]: 1663
% 0.21/0.55  % (23852)Time elapsed: 0.126 s
% 0.21/0.55  % (23852)------------------------------
% 0.21/0.55  % (23852)------------------------------
% 0.21/0.55  % (23843)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (23841)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (23834)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (23844)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (23845)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (23833)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (23835)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (23846)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (23849)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (23840)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (23847)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (23823)Refutation not found, incomplete strategy% (23823)------------------------------
% 0.21/0.57  % (23823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23823)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (23823)Memory used [KB]: 1663
% 0.21/0.57  % (23823)Time elapsed: 0.116 s
% 0.21/0.57  % (23823)------------------------------
% 0.21/0.57  % (23823)------------------------------
% 0.21/0.57  % (23837)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.58/0.57  % (23830)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.58/0.58  % (23848)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.58/0.58  % (23839)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.58/0.58  % (23839)Refutation not found, incomplete strategy% (23839)------------------------------
% 1.58/0.58  % (23839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (23839)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (23839)Memory used [KB]: 10618
% 1.58/0.58  % (23839)Time elapsed: 0.169 s
% 1.58/0.58  % (23839)------------------------------
% 1.58/0.58  % (23839)------------------------------
% 1.58/0.59  % (23828)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.78/0.60  % (23836)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.15/0.67  % (23825)Refutation not found, incomplete strategy% (23825)------------------------------
% 2.15/0.67  % (23825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.67  % (23825)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.67  
% 2.15/0.67  % (23825)Memory used [KB]: 6140
% 2.15/0.67  % (23825)Time elapsed: 0.220 s
% 2.15/0.67  % (23825)------------------------------
% 2.15/0.67  % (23825)------------------------------
% 2.15/0.68  % (23873)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.54/0.73  % (23875)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.54/0.75  % (23874)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.84/0.78  % (23876)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.84/0.84  % (23847)Time limit reached!
% 2.84/0.84  % (23847)------------------------------
% 2.84/0.84  % (23847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.84/0.84  % (23847)Termination reason: Time limit
% 2.84/0.84  % (23847)Termination phase: Saturation
% 2.84/0.84  
% 2.84/0.84  % (23847)Memory used [KB]: 14200
% 2.84/0.84  % (23847)Time elapsed: 0.400 s
% 2.84/0.84  % (23847)------------------------------
% 2.84/0.84  % (23847)------------------------------
% 3.48/0.85  % (23824)Time limit reached!
% 3.48/0.85  % (23824)------------------------------
% 3.48/0.85  % (23824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.85  % (23824)Termination reason: Time limit
% 3.48/0.85  
% 3.48/0.85  % (23824)Memory used [KB]: 6652
% 3.48/0.85  % (23824)Time elapsed: 0.424 s
% 3.48/0.85  % (23824)------------------------------
% 3.48/0.85  % (23824)------------------------------
% 4.21/0.95  % (23877)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.21/0.98  % (23878)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.53/1.03  % (23836)Time limit reached!
% 4.53/1.03  % (23836)------------------------------
% 4.53/1.03  % (23836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.03  % (23836)Termination reason: Time limit
% 4.53/1.03  % (23836)Termination phase: Saturation
% 4.53/1.03  
% 4.53/1.03  % (23836)Memory used [KB]: 5245
% 4.53/1.03  % (23836)Time elapsed: 0.500 s
% 4.53/1.03  % (23836)------------------------------
% 4.53/1.03  % (23836)------------------------------
% 4.53/1.03  % (23828)Time limit reached!
% 4.53/1.03  % (23828)------------------------------
% 4.53/1.03  % (23828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.03  % (23828)Termination reason: Time limit
% 4.53/1.03  % (23828)Termination phase: Saturation
% 4.53/1.03  
% 4.53/1.03  % (23828)Memory used [KB]: 14072
% 4.53/1.03  % (23828)Time elapsed: 0.500 s
% 4.53/1.03  % (23828)------------------------------
% 4.53/1.03  % (23828)------------------------------
% 4.53/1.03  % (23829)Time limit reached!
% 4.53/1.03  % (23829)------------------------------
% 4.53/1.03  % (23829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.03  % (23829)Termination reason: Time limit
% 4.53/1.03  
% 4.53/1.03  % (23829)Memory used [KB]: 10362
% 4.53/1.03  % (23829)Time elapsed: 0.616 s
% 4.53/1.03  % (23829)------------------------------
% 4.53/1.03  % (23829)------------------------------
% 5.41/1.15  % (23880)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.17/1.18  % (23879)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.59/1.21  % (23881)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.06/1.41  % (23834)Time limit reached!
% 8.06/1.41  % (23834)------------------------------
% 8.06/1.41  % (23834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.06/1.41  % (23834)Termination reason: Time limit
% 8.06/1.41  % (23834)Termination phase: Saturation
% 8.06/1.41  
% 8.06/1.41  % (23834)Memory used [KB]: 11641
% 8.06/1.41  % (23834)Time elapsed: 1.0000 s
% 8.06/1.41  % (23834)------------------------------
% 8.06/1.41  % (23834)------------------------------
% 8.58/1.48  % (23874)Refutation found. Thanks to Tanya!
% 8.58/1.48  % SZS status Theorem for theBenchmark
% 8.58/1.48  % SZS output start Proof for theBenchmark
% 8.58/1.48  fof(f5281,plain,(
% 8.58/1.48    $false),
% 8.58/1.48    inference(avatar_sat_refutation,[],[f128,f133,f138,f497,f515,f1787,f1797,f3895,f3942,f4733,f5154,f5280])).
% 8.58/1.48  fof(f5280,plain,(
% 8.58/1.48    spl5_1 | ~spl5_114),
% 8.58/1.48    inference(avatar_contradiction_clause,[],[f5279])).
% 8.58/1.48  fof(f5279,plain,(
% 8.58/1.48    $false | (spl5_1 | ~spl5_114)),
% 8.58/1.48    inference(subsumption_resolution,[],[f5270,f127])).
% 8.58/1.48  fof(f127,plain,(
% 8.58/1.48    sK0 != sK1 | spl5_1),
% 8.58/1.48    inference(avatar_component_clause,[],[f125])).
% 8.58/1.48  fof(f125,plain,(
% 8.58/1.48    spl5_1 <=> sK0 = sK1),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 8.58/1.48  fof(f5270,plain,(
% 8.58/1.48    sK0 = sK1 | ~spl5_114),
% 8.58/1.48    inference(duplicate_literal_removal,[],[f5266])).
% 8.58/1.48  fof(f5266,plain,(
% 8.58/1.48    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl5_114),
% 8.58/1.48    inference(resolution,[],[f5153,f279])).
% 8.58/1.48  fof(f279,plain,(
% 8.58/1.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X2,X2,X2,X2,X2,X1,X0,X0)) | X1 = X3 | X0 = X3 | X2 = X3) )),
% 8.58/1.48    inference(superposition,[],[f123,f104])).
% 8.58/1.48  fof(f104,plain,(
% 8.58/1.48    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f67,f84,f84])).
% 8.58/1.48  fof(f84,plain,(
% 8.58/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f68,f83])).
% 8.58/1.48  fof(f83,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f77,f82])).
% 8.58/1.48  fof(f82,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f78,f80])).
% 8.58/1.48  fof(f80,plain,(
% 8.58/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f19])).
% 8.58/1.48  fof(f19,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 8.58/1.48  fof(f78,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f18])).
% 8.58/1.48  fof(f18,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 8.58/1.48  fof(f77,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f17])).
% 8.58/1.48  fof(f17,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 8.58/1.48  fof(f68,plain,(
% 8.58/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f16])).
% 8.58/1.48  fof(f16,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 8.58/1.48  fof(f67,plain,(
% 8.58/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f10])).
% 8.58/1.48  fof(f10,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 8.58/1.48  fof(f123,plain,(
% 8.58/1.48    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 8.58/1.48    inference(equality_resolution,[],[f112])).
% 8.58/1.48  fof(f112,plain,(
% 8.58/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 8.58/1.48    inference(definition_unfolding,[],[f69,f85])).
% 8.58/1.48  fof(f85,plain,(
% 8.58/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f62,f84])).
% 8.58/1.48  fof(f62,plain,(
% 8.58/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f15])).
% 8.58/1.48  fof(f15,axiom,(
% 8.58/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 8.58/1.48  fof(f69,plain,(
% 8.58/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 8.58/1.48    inference(cnf_transformation,[],[f43])).
% 8.58/1.48  fof(f43,plain,(
% 8.58/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 8.58/1.48  fof(f42,plain,(
% 8.58/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 8.58/1.48    introduced(choice_axiom,[])).
% 8.58/1.48  fof(f41,plain,(
% 8.58/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.58/1.48    inference(rectify,[],[f40])).
% 8.58/1.48  fof(f40,plain,(
% 8.58/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.58/1.48    inference(flattening,[],[f39])).
% 8.58/1.48  fof(f39,plain,(
% 8.58/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.58/1.48    inference(nnf_transformation,[],[f30])).
% 8.58/1.48  fof(f30,plain,(
% 8.58/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 8.58/1.48    inference(ennf_transformation,[],[f8])).
% 8.58/1.48  fof(f8,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 8.58/1.48  fof(f5153,plain,(
% 8.58/1.48    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_114),
% 8.58/1.48    inference(avatar_component_clause,[],[f5151])).
% 8.58/1.48  fof(f5151,plain,(
% 8.58/1.48    spl5_114 <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 8.58/1.48  fof(f5154,plain,(
% 8.58/1.48    spl5_114 | ~spl5_25),
% 8.58/1.48    inference(avatar_split_clause,[],[f5107,f1784,f5151])).
% 8.58/1.48  fof(f1784,plain,(
% 8.58/1.48    spl5_25 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 8.58/1.48  fof(f5107,plain,(
% 8.58/1.48    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_25),
% 8.58/1.48    inference(superposition,[],[f118,f1786])).
% 8.58/1.48  fof(f1786,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl5_25),
% 8.58/1.48    inference(avatar_component_clause,[],[f1784])).
% 8.58/1.48  fof(f118,plain,(
% 8.58/1.48    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 8.58/1.48    inference(equality_resolution,[],[f117])).
% 8.58/1.48  fof(f117,plain,(
% 8.58/1.48    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 8.58/1.48    inference(equality_resolution,[],[f109])).
% 8.58/1.48  fof(f109,plain,(
% 8.58/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 8.58/1.48    inference(definition_unfolding,[],[f72,f85])).
% 8.58/1.48  fof(f72,plain,(
% 8.58/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.58/1.48    inference(cnf_transformation,[],[f43])).
% 8.58/1.48  fof(f4733,plain,(
% 8.58/1.48    spl5_26 | ~spl5_39),
% 8.58/1.48    inference(avatar_split_clause,[],[f4690,f3547,f1794])).
% 8.58/1.48  fof(f1794,plain,(
% 8.58/1.48    spl5_26 <=> r2_hidden(sK0,sK2)),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 8.58/1.48  fof(f3547,plain,(
% 8.58/1.48    spl5_39 <=> sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 8.58/1.48  fof(f4690,plain,(
% 8.58/1.48    r2_hidden(sK0,sK2) | ~spl5_39),
% 8.58/1.48    inference(subsumption_resolution,[],[f4677,f296])).
% 8.58/1.48  fof(f296,plain,(
% 8.58/1.48    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 8.58/1.48    inference(forward_demodulation,[],[f152,f229])).
% 8.58/1.48  fof(f229,plain,(
% 8.58/1.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.58/1.48    inference(forward_demodulation,[],[f228,f48])).
% 8.58/1.48  fof(f48,plain,(
% 8.58/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 8.58/1.48    inference(cnf_transformation,[],[f6])).
% 8.58/1.48  fof(f6,axiom,(
% 8.58/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 8.58/1.48  fof(f228,plain,(
% 8.58/1.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 8.58/1.48    inference(forward_demodulation,[],[f93,f92])).
% 8.58/1.48  fof(f92,plain,(
% 8.58/1.48    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 8.58/1.48    inference(definition_unfolding,[],[f47,f89])).
% 8.58/1.48  fof(f89,plain,(
% 8.58/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f49,f86])).
% 8.58/1.48  fof(f86,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f54,f85])).
% 8.58/1.48  fof(f54,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f14])).
% 8.58/1.48  fof(f14,axiom,(
% 8.58/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 8.58/1.48  fof(f49,plain,(
% 8.58/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f13])).
% 8.58/1.48  fof(f13,axiom,(
% 8.58/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 8.58/1.48  fof(f47,plain,(
% 8.58/1.48    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 8.58/1.48    inference(cnf_transformation,[],[f22])).
% 8.58/1.48  fof(f22,axiom,(
% 8.58/1.48    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 8.58/1.48  fof(f93,plain,(
% 8.58/1.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 8.58/1.48    inference(definition_unfolding,[],[f50,f88])).
% 8.58/1.48  fof(f88,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 8.58/1.48    inference(definition_unfolding,[],[f55,f87])).
% 8.58/1.48  fof(f87,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 8.58/1.48    inference(definition_unfolding,[],[f53,f86])).
% 8.58/1.48  fof(f53,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.58/1.48    inference(cnf_transformation,[],[f21])).
% 8.58/1.48  fof(f21,axiom,(
% 8.58/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 8.58/1.48  fof(f55,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 8.58/1.48    inference(cnf_transformation,[],[f7])).
% 8.58/1.48  fof(f7,axiom,(
% 8.58/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 8.58/1.48  fof(f50,plain,(
% 8.58/1.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.58/1.48    inference(cnf_transformation,[],[f26])).
% 8.58/1.48  fof(f26,plain,(
% 8.58/1.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 8.58/1.48    inference(rectify,[],[f2])).
% 8.58/1.48  fof(f2,axiom,(
% 8.58/1.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 8.58/1.48  fof(f152,plain,(
% 8.58/1.48    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X1))) )),
% 8.58/1.48    inference(superposition,[],[f139,f51])).
% 8.58/1.48  fof(f51,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f1])).
% 8.58/1.48  fof(f1,axiom,(
% 8.58/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 8.58/1.48  fof(f139,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 8.58/1.48    inference(superposition,[],[f63,f48])).
% 8.58/1.48  fof(f63,plain,(
% 8.58/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 8.58/1.48    inference(cnf_transformation,[],[f5])).
% 8.58/1.48  fof(f5,axiom,(
% 8.58/1.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 8.58/1.48  fof(f4677,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) | r2_hidden(sK0,sK2) | ~spl5_39),
% 8.58/1.48    inference(superposition,[],[f474,f3549])).
% 8.58/1.48  fof(f3549,plain,(
% 8.58/1.48    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_39),
% 8.58/1.48    inference(avatar_component_clause,[],[f3547])).
% 8.58/1.48  fof(f474,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) | r2_hidden(X1,X0)) )),
% 8.58/1.48    inference(forward_demodulation,[],[f96,f63])).
% 8.58/1.48  fof(f96,plain,(
% 8.58/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 8.58/1.48    inference(definition_unfolding,[],[f57,f89,f88,f89])).
% 8.58/1.48  fof(f57,plain,(
% 8.58/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 8.58/1.48    inference(cnf_transformation,[],[f29])).
% 8.58/1.48  fof(f29,plain,(
% 8.58/1.48    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 8.58/1.48    inference(ennf_transformation,[],[f20])).
% 8.58/1.48  fof(f20,axiom,(
% 8.58/1.48    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 8.58/1.48  fof(f3942,plain,(
% 8.58/1.48    spl5_39 | ~spl5_59),
% 8.58/1.48    inference(avatar_split_clause,[],[f3899,f3892,f3547])).
% 8.58/1.48  fof(f3892,plain,(
% 8.58/1.48    spl5_59 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 8.58/1.48  fof(f3899,plain,(
% 8.58/1.48    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_59),
% 8.58/1.48    inference(superposition,[],[f297,f3894])).
% 8.58/1.48  fof(f3894,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | ~spl5_59),
% 8.58/1.48    inference(avatar_component_clause,[],[f3892])).
% 8.58/1.48  fof(f297,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X0) )),
% 8.58/1.48    inference(forward_demodulation,[],[f94,f63])).
% 8.58/1.48  fof(f94,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0) )),
% 8.58/1.48    inference(definition_unfolding,[],[f52,f87,f88])).
% 8.58/1.48  fof(f52,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 8.58/1.48    inference(cnf_transformation,[],[f4])).
% 8.58/1.48  fof(f4,axiom,(
% 8.58/1.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 8.58/1.48  fof(f3895,plain,(
% 8.58/1.48    spl5_59 | ~spl5_5),
% 8.58/1.48    inference(avatar_split_clause,[],[f3890,f511,f3892])).
% 8.58/1.48  fof(f511,plain,(
% 8.58/1.48    spl5_5 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 8.58/1.48  fof(f3890,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | ~spl5_5),
% 8.58/1.48    inference(forward_demodulation,[],[f513,f599])).
% 8.58/1.48  fof(f599,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X5)) )),
% 8.58/1.48    inference(superposition,[],[f113,f90])).
% 8.58/1.48  fof(f90,plain,(
% 8.58/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)))) )),
% 8.58/1.48    inference(definition_unfolding,[],[f81,f87,f83,f85])).
% 8.58/1.48  fof(f81,plain,(
% 8.58/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 8.58/1.48    inference(cnf_transformation,[],[f12])).
% 8.58/1.48  fof(f12,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 8.58/1.48  fof(f113,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))) )),
% 8.58/1.48    inference(definition_unfolding,[],[f79,f82,f87,f83,f89])).
% 8.58/1.48  fof(f79,plain,(
% 8.58/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 8.58/1.48    inference(cnf_transformation,[],[f11])).
% 8.58/1.48  fof(f11,axiom,(
% 8.58/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 8.58/1.48  fof(f513,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | ~spl5_5),
% 8.58/1.48    inference(avatar_component_clause,[],[f511])).
% 8.58/1.48  fof(f1797,plain,(
% 8.58/1.48    ~spl5_26 | ~spl5_2 | spl5_24),
% 8.58/1.48    inference(avatar_split_clause,[],[f1792,f1780,f130,f1794])).
% 8.58/1.48  fof(f130,plain,(
% 8.58/1.48    spl5_2 <=> r2_hidden(sK1,sK2)),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 8.58/1.48  fof(f1780,plain,(
% 8.58/1.48    spl5_24 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 8.58/1.48  fof(f1792,plain,(
% 8.58/1.48    ~r2_hidden(sK0,sK2) | (~spl5_2 | spl5_24)),
% 8.58/1.48    inference(subsumption_resolution,[],[f1789,f132])).
% 8.58/1.48  fof(f132,plain,(
% 8.58/1.48    r2_hidden(sK1,sK2) | ~spl5_2),
% 8.58/1.48    inference(avatar_component_clause,[],[f130])).
% 8.58/1.48  fof(f1789,plain,(
% 8.58/1.48    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | spl5_24),
% 8.58/1.48    inference(resolution,[],[f1782,f101])).
% 8.58/1.48  fof(f101,plain,(
% 8.58/1.48    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f66,f86])).
% 8.58/1.48  fof(f66,plain,(
% 8.58/1.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f38])).
% 8.58/1.48  fof(f38,plain,(
% 8.58/1.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 8.58/1.48    inference(flattening,[],[f37])).
% 8.58/1.48  fof(f37,plain,(
% 8.58/1.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 8.58/1.48    inference(nnf_transformation,[],[f23])).
% 8.58/1.48  fof(f23,axiom,(
% 8.58/1.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 8.58/1.48  fof(f1782,plain,(
% 8.58/1.48    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | spl5_24),
% 8.58/1.48    inference(avatar_component_clause,[],[f1780])).
% 8.58/1.48  fof(f1787,plain,(
% 8.58/1.48    ~spl5_24 | spl5_25 | ~spl5_4),
% 8.58/1.48    inference(avatar_split_clause,[],[f1778,f494,f1784,f1780])).
% 8.58/1.48  fof(f494,plain,(
% 8.58/1.48    spl5_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 8.58/1.48  fof(f1778,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl5_4),
% 8.58/1.48    inference(forward_demodulation,[],[f1777,f229])).
% 8.58/1.48  fof(f1777,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl5_4),
% 8.58/1.48    inference(forward_demodulation,[],[f1776,f139])).
% 8.58/1.48  fof(f1776,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl5_4),
% 8.58/1.48    inference(forward_demodulation,[],[f1770,f51])).
% 8.58/1.48  fof(f1770,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl5_4),
% 8.58/1.48    inference(superposition,[],[f496,f262])).
% 8.58/1.48  fof(f262,plain,(
% 8.58/1.48    ( ! [X8,X7] : (k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X7,X7,X7)) = X8 | ~r1_tarski(X7,X8)) )),
% 8.58/1.48    inference(superposition,[],[f95,f104])).
% 8.58/1.48  fof(f95,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 8.58/1.48    inference(definition_unfolding,[],[f56,f87])).
% 8.58/1.48  fof(f56,plain,(
% 8.58/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 8.58/1.48    inference(cnf_transformation,[],[f28])).
% 8.58/1.48  fof(f28,plain,(
% 8.58/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.58/1.48    inference(ennf_transformation,[],[f3])).
% 8.58/1.48  fof(f3,axiom,(
% 8.58/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 8.58/1.48  fof(f496,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl5_4),
% 8.58/1.48    inference(avatar_component_clause,[],[f494])).
% 8.58/1.48  fof(f515,plain,(
% 8.58/1.48    spl5_5 | ~spl5_4),
% 8.58/1.48    inference(avatar_split_clause,[],[f500,f494,f511])).
% 8.58/1.48  fof(f500,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | ~spl5_4),
% 8.58/1.48    inference(superposition,[],[f63,f496])).
% 8.58/1.48  fof(f497,plain,(
% 8.58/1.48    spl5_4 | ~spl5_3),
% 8.58/1.48    inference(avatar_split_clause,[],[f492,f135,f494])).
% 8.58/1.48  fof(f135,plain,(
% 8.58/1.48    spl5_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))),
% 8.58/1.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 8.58/1.48  fof(f492,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl5_3),
% 8.58/1.48    inference(forward_demodulation,[],[f491,f51])).
% 8.58/1.48  fof(f491,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl5_3),
% 8.58/1.48    inference(forward_demodulation,[],[f137,f104])).
% 8.58/1.48  fof(f137,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) | ~spl5_3),
% 8.58/1.48    inference(avatar_component_clause,[],[f135])).
% 8.58/1.48  fof(f138,plain,(
% 8.58/1.48    spl5_3),
% 8.58/1.48    inference(avatar_split_clause,[],[f91,f135])).
% 8.58/1.48  fof(f91,plain,(
% 8.58/1.48    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))),
% 8.58/1.48    inference(definition_unfolding,[],[f44,f89,f88,f86])).
% 8.58/1.48  fof(f44,plain,(
% 8.58/1.48    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.58/1.48    inference(cnf_transformation,[],[f32])).
% 8.58/1.48  fof(f32,plain,(
% 8.58/1.48    sK0 != sK1 & r2_hidden(sK1,sK2) & k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).
% 8.58/1.48  fof(f31,plain,(
% 8.58/1.48    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2)) => (sK0 != sK1 & r2_hidden(sK1,sK2) & k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 8.58/1.48    introduced(choice_axiom,[])).
% 8.58/1.48  fof(f27,plain,(
% 8.58/1.48    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 8.58/1.48    inference(ennf_transformation,[],[f25])).
% 8.58/1.48  fof(f25,negated_conjecture,(
% 8.58/1.48    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 8.58/1.48    inference(negated_conjecture,[],[f24])).
% 8.58/1.48  fof(f24,conjecture,(
% 8.58/1.48    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 8.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 8.58/1.48  fof(f133,plain,(
% 8.58/1.48    spl5_2),
% 8.58/1.48    inference(avatar_split_clause,[],[f45,f130])).
% 8.58/1.48  fof(f45,plain,(
% 8.58/1.48    r2_hidden(sK1,sK2)),
% 8.58/1.48    inference(cnf_transformation,[],[f32])).
% 8.58/1.48  fof(f128,plain,(
% 8.58/1.48    ~spl5_1),
% 8.58/1.48    inference(avatar_split_clause,[],[f46,f125])).
% 8.58/1.48  fof(f46,plain,(
% 8.58/1.48    sK0 != sK1),
% 8.58/1.48    inference(cnf_transformation,[],[f32])).
% 8.58/1.48  % SZS output end Proof for theBenchmark
% 8.58/1.48  % (23874)------------------------------
% 8.58/1.48  % (23874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.58/1.48  % (23874)Termination reason: Refutation
% 8.58/1.48  
% 8.58/1.48  % (23874)Memory used [KB]: 17782
% 8.58/1.48  % (23874)Time elapsed: 0.850 s
% 8.58/1.48  % (23874)------------------------------
% 8.58/1.48  % (23874)------------------------------
% 8.58/1.48  % (23821)Success in time 1.111 s
%------------------------------------------------------------------------------
