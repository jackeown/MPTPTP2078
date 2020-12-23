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
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 225 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  247 ( 571 expanded)
%              Number of equality atoms :   27 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f994,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f836,f852,f853,f854,f882,f924,f993])).

fof(f993,plain,
    ( ~ spl6_9
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | ~ spl6_9
    | spl6_26 ),
    inference(resolution,[],[f874,f856])).

fof(f856,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f254,f145])).

fof(f145,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f46,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f254,plain,
    ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl6_9
  <=> ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f874,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f872])).

fof(f872,plain,
    ( spl6_26
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f924,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f920])).

fof(f920,plain,
    ( $false
    | spl6_27 ),
    inference(resolution,[],[f886,f38])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f886,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_27 ),
    inference(resolution,[],[f881,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f881,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl6_27
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f882,plain,
    ( ~ spl6_27
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f175,f872,f879])).

fof(f175,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f64,f53])).

fof(f64,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f854,plain,
    ( ~ spl6_11
    | spl6_23 ),
    inference(avatar_split_clause,[],[f742,f841,f320])).

fof(f320,plain,
    ( spl6_11
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f841,plain,
    ( spl6_23
  <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f742,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f201,f65])).

fof(f65,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f201,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X16,X15)
      | r1_xboole_0(X15,X16)
      | k1_xboole_0 != X16 ) ),
    inference(superposition,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f853,plain,
    ( spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f274,f256,f320])).

fof(f256,plain,
    ( spl6_10
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f274,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f97,f65])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f54,f52])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f852,plain,
    ( spl6_9
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f554,f841,f253])).

fof(f554,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f170,f65])).

fof(f170,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_xboole_0(X4,X3)
      | ~ r2_hidden(X5,X3) ) ),
    inference(superposition,[],[f76,f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f47,f43])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f836,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | spl6_10 ),
    inference(resolution,[],[f817,f38])).

fof(f817,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_10 ),
    inference(resolution,[],[f577,f280])).

fof(f280,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl6_10 ),
    inference(resolution,[],[f266,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f266,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(resolution,[],[f261,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f261,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(resolution,[],[f258,f53])).

fof(f258,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f256])).

fof(f577,plain,(
    ! [X6,X4,X5] :
      ( r1_xboole_0(k3_xboole_0(X6,X5),X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f184,f72])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X2,X0) ) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f49,f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:24:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (23353)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.44  % (23351)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (23347)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (23358)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (23346)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (23356)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (23355)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (23354)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (23352)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (23347)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f994,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f836,f852,f853,f854,f882,f924,f993])).
% 0.20/0.48  fof(f993,plain,(
% 0.20/0.48    ~spl6_9 | spl6_26),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f989])).
% 0.20/0.48  fof(f989,plain,(
% 0.20/0.48    $false | (~spl6_9 | spl6_26)),
% 0.20/0.48    inference(resolution,[],[f874,f856])).
% 0.20/0.48  fof(f856,plain,(
% 0.20/0.48    r1_xboole_0(sK1,sK0) | ~spl6_9),
% 0.20/0.48    inference(resolution,[],[f254,f145])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 0.20/0.48    inference(superposition,[],[f46,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k3_xboole_0(sK0,sK1))) ) | ~spl6_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f253])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    spl6_9 <=> ! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.48  fof(f874,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1,sK0) | spl6_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f872])).
% 0.20/0.48  fof(f872,plain,(
% 0.20/0.48    spl6_26 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.48  fof(f924,plain,(
% 0.20/0.48    spl6_27),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f920])).
% 0.20/0.48  fof(f920,plain,(
% 0.20/0.48    $false | spl6_27),
% 0.20/0.48    inference(resolution,[],[f886,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    r1_xboole_0(sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f16])).
% 0.20/0.48  fof(f16,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.20/0.48  fof(f886,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK1) | spl6_27),
% 0.20/0.48    inference(resolution,[],[f881,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.48  fof(f881,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1,sK2) | spl6_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f879])).
% 0.20/0.48  fof(f879,plain,(
% 0.20/0.48    spl6_27 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.48  fof(f882,plain,(
% 0.20/0.48    ~spl6_27 | ~spl6_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f175,f872,f879])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 0.20/0.48    inference(resolution,[],[f69,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 0.20/0.48    inference(resolution,[],[f64,f53])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.20/0.48    inference(definition_unfolding,[],[f39,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f44,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f45,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f57,f62])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.48  fof(f854,plain,(
% 0.20/0.48    ~spl6_11 | spl6_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f742,f841,f320])).
% 0.20/0.48  fof(f320,plain,(
% 0.20/0.48    spl6_11 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.48  fof(f841,plain,(
% 0.20/0.48    spl6_23 <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.48  fof(f742,plain,(
% 0.20/0.48    r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f201,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.48    inference(definition_unfolding,[],[f36,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f41,f61])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    ( ! [X15,X16] : (~r1_tarski(X16,X15) | r1_xboole_0(X15,X16) | k1_xboole_0 != X16) )),
% 0.20/0.48    inference(superposition,[],[f55,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.20/0.48    inference(superposition,[],[f52,f43])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.48  fof(f853,plain,(
% 0.20/0.48    spl6_11 | ~spl6_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f274,f256,f320])).
% 0.20/0.48  fof(f256,plain,(
% 0.20/0.48    spl6_10 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f97,f65])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 0.20/0.48    inference(superposition,[],[f54,f52])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f852,plain,(
% 0.20/0.48    spl6_9 | ~spl6_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f554,f841,f253])).
% 0.20/0.48  fof(f554,plain,(
% 0.20/0.48    ( ! [X3] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | ~r2_hidden(X3,k3_xboole_0(sK0,sK1))) )),
% 0.20/0.48    inference(resolution,[],[f170,f65])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | ~r1_xboole_0(X4,X3) | ~r2_hidden(X5,X3)) )),
% 0.20/0.48    inference(superposition,[],[f76,f52])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(superposition,[],[f47,f43])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f836,plain,(
% 0.20/0.48    spl6_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f832])).
% 0.20/0.48  fof(f832,plain,(
% 0.20/0.48    $false | spl6_10),
% 0.20/0.48    inference(resolution,[],[f817,f38])).
% 0.20/0.48  fof(f817,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK1) | spl6_10),
% 0.20/0.48    inference(resolution,[],[f577,f280])).
% 0.20/0.48  fof(f280,plain,(
% 0.20/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl6_10),
% 0.20/0.48    inference(resolution,[],[f266,f137])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.20/0.48    inference(resolution,[],[f50,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    r2_hidden(sK3,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl6_10),
% 0.20/0.48    inference(resolution,[],[f261,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f51,f63])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl6_10),
% 0.20/0.48    inference(resolution,[],[f258,f53])).
% 0.20/0.48  fof(f258,plain,(
% 0.20/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f256])).
% 0.20/0.48  fof(f577,plain,(
% 0.20/0.48    ( ! [X6,X4,X5] : (r1_xboole_0(k3_xboole_0(X6,X5),X4) | ~r1_xboole_0(X4,X5)) )),
% 0.20/0.48    inference(resolution,[],[f184,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.48    inference(superposition,[],[f42,f43])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X2,X0)) )),
% 0.20/0.48    inference(resolution,[],[f79,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) )),
% 0.20/0.48    inference(resolution,[],[f49,f47])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23347)------------------------------
% 0.20/0.48  % (23347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23347)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23347)Memory used [KB]: 6396
% 0.20/0.48  % (23347)Time elapsed: 0.054 s
% 0.20/0.48  % (23347)------------------------------
% 0.20/0.48  % (23347)------------------------------
% 0.20/0.48  % (23342)Success in time 0.126 s
%------------------------------------------------------------------------------
