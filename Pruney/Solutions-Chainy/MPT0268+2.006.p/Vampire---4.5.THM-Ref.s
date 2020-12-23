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
% DateTime   : Thu Dec  3 12:40:36 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 209 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  318 ( 671 expanded)
%              Number of equality atoms :  147 ( 397 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f446,f989,f1039,f1066])).

fof(f1066,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f1065])).

fof(f1065,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f1044,f1011])).

fof(f1011,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(sK0,k3_enumset1(X0,X0,X0,X1,sK1))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f137,f163,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f163,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f137,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f93,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).

fof(f52,plain,(
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

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1044,plain,
    ( r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_1 ),
    inference(superposition,[],[f60,f158])).

fof(f158,plain,
    ( sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_1
  <=> sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1039,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f993,f161,f157])).

fof(f993,plain,
    ( sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f103,f163])).

fof(f103,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f54,f100])).

fof(f100,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f98])).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f989,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f988])).

fof(f988,plain,
    ( $false
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f987,f817])).

fof(f817,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f265,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f265,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f137,f137,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f88,f99])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f987,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl6_2
    | spl6_3 ),
    inference(backward_demodulation,[],[f683,f963])).

fof(f963,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f59,f436,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f72,f100,f100])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f436,plain,
    ( ! [X0] : k1_xboole_0 != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,sK1),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f241,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f241,plain,
    ( ! [X0] : ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK1),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f87,f99])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f162,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f161])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f683,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f445,f215])).

fof(f215,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 != k4_xboole_0(X13,k4_xboole_0(X13,X12))
      | r1_tarski(X12,k4_xboole_0(X12,X13)) ) ),
    inference(superposition,[],[f75,f104])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f61,f63,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f445,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl6_3
  <=> r1_tarski(sK0,k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f446,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f180,f157,f443])).

fof(f180,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f159,f59,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f159,plain,
    ( sK0 != k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f164,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f102,f161,f157])).

fof(f102,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f55,f100])).

fof(f55,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (9435)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (9431)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (9427)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (9451)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (9429)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (9430)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (9427)Refutation not found, incomplete strategy% (9427)------------------------------
% 0.21/0.52  % (9427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9427)Memory used [KB]: 1663
% 0.21/0.52  % (9427)Time elapsed: 0.110 s
% 0.21/0.52  % (9427)------------------------------
% 0.21/0.52  % (9427)------------------------------
% 0.21/0.52  % (9449)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (9447)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (9445)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (9439)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (9441)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (9426)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (9453)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (9434)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (9454)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (9452)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (9452)Refutation not found, incomplete strategy% (9452)------------------------------
% 0.21/0.54  % (9452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9452)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9452)Memory used [KB]: 6268
% 0.21/0.54  % (9452)Time elapsed: 0.136 s
% 0.21/0.54  % (9452)------------------------------
% 0.21/0.54  % (9452)------------------------------
% 0.21/0.54  % (9433)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (9428)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (9432)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (9450)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (9455)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (9455)Refutation not found, incomplete strategy% (9455)------------------------------
% 0.21/0.55  % (9455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9455)Memory used [KB]: 1663
% 0.21/0.55  % (9455)Time elapsed: 0.002 s
% 0.21/0.55  % (9455)------------------------------
% 0.21/0.55  % (9455)------------------------------
% 0.21/0.55  % (9444)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (9446)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (9437)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (9436)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (9437)Refutation not found, incomplete strategy% (9437)------------------------------
% 0.21/0.56  % (9437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9437)Memory used [KB]: 6268
% 0.21/0.56  % (9437)Time elapsed: 0.152 s
% 0.21/0.56  % (9437)------------------------------
% 0.21/0.56  % (9437)------------------------------
% 0.21/0.56  % (9438)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (9436)Refutation not found, incomplete strategy% (9436)------------------------------
% 0.21/0.56  % (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9438)Refutation not found, incomplete strategy% (9438)------------------------------
% 0.21/0.56  % (9438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9438)Memory used [KB]: 10618
% 0.21/0.56  % (9438)Time elapsed: 0.159 s
% 0.21/0.56  % (9438)------------------------------
% 0.21/0.56  % (9438)------------------------------
% 0.21/0.56  % (9436)Memory used [KB]: 10746
% 0.21/0.56  % (9436)Time elapsed: 0.160 s
% 0.21/0.56  % (9436)------------------------------
% 0.21/0.56  % (9436)------------------------------
% 1.55/0.56  % (9448)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.56  % (9443)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.57  % (9442)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.57  % (9443)Refutation not found, incomplete strategy% (9443)------------------------------
% 1.55/0.57  % (9443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (9443)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (9443)Memory used [KB]: 1791
% 1.55/0.57  % (9443)Time elapsed: 0.131 s
% 1.55/0.57  % (9443)------------------------------
% 1.55/0.57  % (9443)------------------------------
% 1.55/0.57  % (9440)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.57  % (9440)Refutation not found, incomplete strategy% (9440)------------------------------
% 1.55/0.57  % (9440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (9440)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (9440)Memory used [KB]: 1663
% 1.55/0.57  % (9440)Time elapsed: 0.143 s
% 1.55/0.57  % (9440)------------------------------
% 1.55/0.57  % (9440)------------------------------
% 1.75/0.58  % (9442)Refutation not found, incomplete strategy% (9442)------------------------------
% 1.75/0.58  % (9442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.58  % (9442)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.58  
% 1.75/0.58  % (9442)Memory used [KB]: 10618
% 1.75/0.58  % (9442)Time elapsed: 0.178 s
% 1.75/0.58  % (9442)------------------------------
% 1.75/0.58  % (9442)------------------------------
% 2.15/0.65  % (9446)Refutation found. Thanks to Tanya!
% 2.15/0.65  % SZS status Theorem for theBenchmark
% 2.15/0.65  % SZS output start Proof for theBenchmark
% 2.15/0.65  fof(f1079,plain,(
% 2.15/0.65    $false),
% 2.15/0.65    inference(avatar_sat_refutation,[],[f164,f446,f989,f1039,f1066])).
% 2.15/0.65  fof(f1066,plain,(
% 2.15/0.65    ~spl6_1 | ~spl6_2),
% 2.15/0.65    inference(avatar_contradiction_clause,[],[f1065])).
% 2.15/0.65  fof(f1065,plain,(
% 2.15/0.65    $false | (~spl6_1 | ~spl6_2)),
% 2.15/0.65    inference(subsumption_resolution,[],[f1044,f1011])).
% 2.15/0.65  fof(f1011,plain,(
% 2.15/0.65    ( ! [X0,X1] : (~r1_xboole_0(sK0,k3_enumset1(X0,X0,X0,X1,sK1))) ) | ~spl6_2),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f137,f163,f67])).
% 2.15/0.65  fof(f67,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f35])).
% 2.15/0.65  fof(f35,plain,(
% 2.15/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.15/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f34])).
% 2.15/0.65  fof(f34,plain,(
% 2.15/0.65    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.15/0.65    introduced(choice_axiom,[])).
% 2.15/0.65  fof(f26,plain,(
% 2.15/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.15/0.65    inference(ennf_transformation,[],[f23])).
% 2.15/0.65  fof(f23,plain,(
% 2.15/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.15/0.65    inference(rectify,[],[f3])).
% 2.15/0.65  fof(f3,axiom,(
% 2.15/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.15/0.65  fof(f163,plain,(
% 2.15/0.65    r2_hidden(sK1,sK0) | ~spl6_2),
% 2.15/0.65    inference(avatar_component_clause,[],[f161])).
% 2.15/0.65  fof(f161,plain,(
% 2.15/0.65    spl6_2 <=> r2_hidden(sK1,sK0)),
% 2.15/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.15/0.65  fof(f137,plain,(
% 2.15/0.65    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 2.15/0.65    inference(equality_resolution,[],[f136])).
% 2.15/0.65  fof(f136,plain,(
% 2.15/0.65    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 2.15/0.65    inference(equality_resolution,[],[f124])).
% 2.15/0.65  fof(f124,plain,(
% 2.15/0.65    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.15/0.65    inference(definition_unfolding,[],[f93,f98])).
% 2.15/0.65  fof(f98,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.15/0.65    inference(definition_unfolding,[],[f79,f89])).
% 2.15/0.65  fof(f89,plain,(
% 2.15/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f17])).
% 2.15/0.65  fof(f17,axiom,(
% 2.15/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.15/0.65  fof(f79,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f16])).
% 2.15/0.65  fof(f16,axiom,(
% 2.15/0.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.15/0.65  fof(f93,plain,(
% 2.15/0.65    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.15/0.65    inference(cnf_transformation,[],[f53])).
% 2.15/0.65  fof(f53,plain,(
% 2.15/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.15/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).
% 2.15/0.65  fof(f52,plain,(
% 2.15/0.65    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 2.15/0.65    introduced(choice_axiom,[])).
% 2.15/0.65  fof(f51,plain,(
% 2.15/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.15/0.65    inference(rectify,[],[f50])).
% 2.15/0.65  fof(f50,plain,(
% 2.15/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.15/0.65    inference(flattening,[],[f49])).
% 2.15/0.65  fof(f49,plain,(
% 2.15/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.15/0.65    inference(nnf_transformation,[],[f28])).
% 2.15/0.65  fof(f28,plain,(
% 2.15/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.15/0.65    inference(ennf_transformation,[],[f13])).
% 2.15/0.65  fof(f13,axiom,(
% 2.15/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.15/0.65  fof(f1044,plain,(
% 2.15/0.65    r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_1),
% 2.15/0.65    inference(superposition,[],[f60,f158])).
% 2.15/0.65  fof(f158,plain,(
% 2.15/0.65    sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_1),
% 2.15/0.65    inference(avatar_component_clause,[],[f157])).
% 2.15/0.65  fof(f157,plain,(
% 2.15/0.65    spl6_1 <=> sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.15/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.15/0.65  fof(f60,plain,(
% 2.15/0.65    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f12])).
% 2.15/0.65  fof(f12,axiom,(
% 2.15/0.65    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.15/0.65  fof(f1039,plain,(
% 2.15/0.65    spl6_1 | ~spl6_2),
% 2.15/0.65    inference(avatar_split_clause,[],[f993,f161,f157])).
% 2.15/0.65  fof(f993,plain,(
% 2.15/0.65    sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_2),
% 2.15/0.65    inference(subsumption_resolution,[],[f103,f163])).
% 2.15/0.65  fof(f103,plain,(
% 2.15/0.65    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.15/0.65    inference(definition_unfolding,[],[f54,f100])).
% 2.15/0.65  fof(f100,plain,(
% 2.15/0.65    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.15/0.65    inference(definition_unfolding,[],[f57,f99])).
% 2.15/0.65  fof(f99,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.15/0.65    inference(definition_unfolding,[],[f62,f98])).
% 2.15/0.65  fof(f62,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f15])).
% 2.15/0.65  fof(f15,axiom,(
% 2.15/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.15/0.65  fof(f57,plain,(
% 2.15/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f14])).
% 2.15/0.65  fof(f14,axiom,(
% 2.15/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.15/0.65  fof(f54,plain,(
% 2.15/0.65    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.15/0.65    inference(cnf_transformation,[],[f31])).
% 2.15/0.65  fof(f31,plain,(
% 2.15/0.65    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 2.15/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 2.15/0.65  fof(f30,plain,(
% 2.15/0.65    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 2.15/0.65    introduced(choice_axiom,[])).
% 2.15/0.65  fof(f29,plain,(
% 2.15/0.65    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 2.15/0.65    inference(nnf_transformation,[],[f24])).
% 2.15/0.65  fof(f24,plain,(
% 2.15/0.65    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.15/0.65    inference(ennf_transformation,[],[f22])).
% 2.15/0.65  fof(f22,negated_conjecture,(
% 2.15/0.65    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.15/0.65    inference(negated_conjecture,[],[f21])).
% 2.15/0.65  fof(f21,conjecture,(
% 2.15/0.65    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.15/0.65  fof(f989,plain,(
% 2.15/0.65    spl6_2 | spl6_3),
% 2.15/0.65    inference(avatar_contradiction_clause,[],[f988])).
% 2.15/0.65  fof(f988,plain,(
% 2.15/0.65    $false | (spl6_2 | spl6_3)),
% 2.15/0.65    inference(subsumption_resolution,[],[f987,f817])).
% 2.15/0.65  fof(f817,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X2,X0))) )),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f265,f76])).
% 2.15/0.65  fof(f76,plain,(
% 2.15/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f40])).
% 2.15/0.65  fof(f40,plain,(
% 2.15/0.65    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.15/0.65    inference(nnf_transformation,[],[f6])).
% 2.15/0.65  fof(f6,axiom,(
% 2.15/0.65    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.15/0.65  fof(f265,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X2,X0))) )),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f137,f137,f117])).
% 2.15/0.65  fof(f117,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.15/0.65    inference(definition_unfolding,[],[f88,f99])).
% 2.15/0.65  fof(f88,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f48])).
% 2.15/0.65  fof(f48,plain,(
% 2.15/0.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.15/0.65    inference(flattening,[],[f47])).
% 2.15/0.65  fof(f47,plain,(
% 2.15/0.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.15/0.65    inference(nnf_transformation,[],[f20])).
% 2.15/0.65  fof(f20,axiom,(
% 2.15/0.65    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.15/0.65  fof(f987,plain,(
% 2.15/0.65    k1_xboole_0 != k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (spl6_2 | spl6_3)),
% 2.15/0.65    inference(backward_demodulation,[],[f683,f963])).
% 2.15/0.65  fof(f963,plain,(
% 2.15/0.65    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | spl6_2),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f59,f436,f108])).
% 2.15/0.65  fof(f108,plain,(
% 2.15/0.65    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 2.15/0.65    inference(definition_unfolding,[],[f72,f100,f100])).
% 2.15/0.65  fof(f72,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.15/0.65    inference(cnf_transformation,[],[f39])).
% 2.15/0.65  fof(f39,plain,(
% 2.15/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.15/0.65    inference(flattening,[],[f38])).
% 2.15/0.65  fof(f38,plain,(
% 2.15/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.15/0.65    inference(nnf_transformation,[],[f18])).
% 2.15/0.65  fof(f18,axiom,(
% 2.15/0.65    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.15/0.65  fof(f436,plain,(
% 2.15/0.65    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,sK1),sK0)) ) | spl6_2),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f241,f75])).
% 2.15/0.65  fof(f75,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f40])).
% 2.15/0.65  fof(f241,plain,(
% 2.15/0.65    ( ! [X0] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,sK1),sK0)) ) | spl6_2),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f162,f118])).
% 2.15/0.65  fof(f118,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.15/0.65    inference(definition_unfolding,[],[f87,f99])).
% 2.15/0.65  fof(f87,plain,(
% 2.15/0.65    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f48])).
% 2.15/0.65  fof(f162,plain,(
% 2.15/0.65    ~r2_hidden(sK1,sK0) | spl6_2),
% 2.15/0.65    inference(avatar_component_clause,[],[f161])).
% 2.15/0.65  fof(f59,plain,(
% 2.15/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f9])).
% 2.15/0.65  fof(f9,axiom,(
% 2.15/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.15/0.65  fof(f683,plain,(
% 2.15/0.65    k1_xboole_0 != k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)) | spl6_3),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f445,f215])).
% 2.15/0.65  fof(f215,plain,(
% 2.15/0.65    ( ! [X12,X13] : (k1_xboole_0 != k4_xboole_0(X13,k4_xboole_0(X13,X12)) | r1_tarski(X12,k4_xboole_0(X12,X13))) )),
% 2.15/0.65    inference(superposition,[],[f75,f104])).
% 2.15/0.65  fof(f104,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.15/0.65    inference(definition_unfolding,[],[f61,f63,f63])).
% 2.15/0.65  fof(f63,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.15/0.65    inference(cnf_transformation,[],[f10])).
% 2.15/0.65  fof(f10,axiom,(
% 2.15/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.15/0.65  fof(f61,plain,(
% 2.15/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f1])).
% 2.15/0.65  fof(f1,axiom,(
% 2.15/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.15/0.65  fof(f445,plain,(
% 2.15/0.65    ~r1_tarski(sK0,k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl6_3),
% 2.15/0.65    inference(avatar_component_clause,[],[f443])).
% 2.15/0.65  fof(f443,plain,(
% 2.15/0.65    spl6_3 <=> r1_tarski(sK0,k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 2.15/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.15/0.65  fof(f446,plain,(
% 2.15/0.65    ~spl6_3 | spl6_1),
% 2.15/0.65    inference(avatar_split_clause,[],[f180,f157,f443])).
% 2.15/0.65  fof(f180,plain,(
% 2.15/0.65    ~r1_tarski(sK0,k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl6_1),
% 2.15/0.65    inference(unit_resulting_resolution,[],[f159,f59,f71])).
% 2.15/0.65  fof(f71,plain,(
% 2.15/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.15/0.65    inference(cnf_transformation,[],[f37])).
% 2.15/0.65  fof(f37,plain,(
% 2.15/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.65    inference(flattening,[],[f36])).
% 2.15/0.65  fof(f36,plain,(
% 2.15/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.65    inference(nnf_transformation,[],[f5])).
% 2.15/0.65  fof(f5,axiom,(
% 2.15/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.15/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.15/0.65  fof(f159,plain,(
% 2.15/0.65    sK0 != k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl6_1),
% 2.15/0.65    inference(avatar_component_clause,[],[f157])).
% 2.15/0.65  fof(f164,plain,(
% 2.15/0.65    ~spl6_1 | spl6_2),
% 2.15/0.65    inference(avatar_split_clause,[],[f102,f161,f157])).
% 2.15/0.65  fof(f102,plain,(
% 2.15/0.65    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.15/0.65    inference(definition_unfolding,[],[f55,f100])).
% 2.15/0.65  fof(f55,plain,(
% 2.15/0.65    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.15/0.65    inference(cnf_transformation,[],[f31])).
% 2.15/0.65  % SZS output end Proof for theBenchmark
% 2.15/0.65  % (9446)------------------------------
% 2.15/0.65  % (9446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.65  % (9446)Termination reason: Refutation
% 2.15/0.65  
% 2.15/0.65  % (9446)Memory used [KB]: 11641
% 2.15/0.65  % (9446)Time elapsed: 0.250 s
% 2.15/0.65  % (9446)------------------------------
% 2.15/0.65  % (9446)------------------------------
% 2.15/0.65  % (9425)Success in time 0.288 s
%------------------------------------------------------------------------------
