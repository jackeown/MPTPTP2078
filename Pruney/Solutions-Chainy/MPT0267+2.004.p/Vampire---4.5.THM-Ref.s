%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:34 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 253 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  278 ( 619 expanded)
%              Number of equality atoms :   82 ( 228 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f93,f94,f170,f204,f217])).

fof(f217,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f213,f73])).

fof(f73,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f213,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f92,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f43,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f92,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f204,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f195,f174])).

fof(f174,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f173,f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f173,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_1 ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f77,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f195,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_1 ),
    inference(resolution,[],[f148,f77])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f100,f67])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f39,f39])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f170,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f163,f85])).

fof(f85,plain,
    ( sK0 != sK2
    | spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f163,plain,
    ( sK0 = sK2
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f145])).

fof(f145,plain,
    ( r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f138,f81])).

fof(f81,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f138,plain,
    ( r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0,sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f123,f136])).

fof(f136,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f135,f81])).

fof(f135,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f123,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_xboole_0(X11,X10))
      | r2_hidden(X9,X10)
      | ~ r2_hidden(X9,X11) ) ),
    inference(resolution,[],[f52,f101])).

fof(f101,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X5,k3_xboole_0(X4,X5)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f43,f96])).

fof(f96,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f66,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f65,f80,f76])).

fof(f65,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f32,f39,f62])).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK0 = sK2
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
    & ( ( sK0 != sK2
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK0 = sK2
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
      & ( ( sK0 != sK2
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f18])).

% (15443)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f18,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f93,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f88,f84,f90])).

fof(f88,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f33,f39,f62])).

fof(f33,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f63,f84,f80,f76])).

fof(f63,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f34,f39,f62])).

fof(f34,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (15447)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (15424)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (15430)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.51  % (15427)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.18/0.51  % (15439)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.18/0.51  % (15432)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.18/0.51  % (15439)Refutation not found, incomplete strategy% (15439)------------------------------
% 1.18/0.51  % (15439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.51  % (15439)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.51  
% 1.18/0.51  % (15439)Memory used [KB]: 1663
% 1.18/0.51  % (15439)Time elapsed: 0.104 s
% 1.18/0.51  % (15439)------------------------------
% 1.18/0.51  % (15439)------------------------------
% 1.18/0.51  % (15428)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.18/0.52  % (15440)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.18/0.52  % (15438)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.18/0.52  % (15430)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % (15446)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.18/0.52  % (15448)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  fof(f219,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(avatar_sat_refutation,[],[f87,f93,f94,f170,f204,f217])).
% 1.18/0.52  fof(f217,plain,(
% 1.18/0.52    ~spl5_4),
% 1.18/0.52    inference(avatar_contradiction_clause,[],[f216])).
% 1.18/0.52  fof(f216,plain,(
% 1.18/0.52    $false | ~spl5_4),
% 1.18/0.52    inference(subsumption_resolution,[],[f213,f73])).
% 1.18/0.52  fof(f73,plain,(
% 1.18/0.52    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.18/0.52    inference(equality_resolution,[],[f72])).
% 1.18/0.52  fof(f72,plain,(
% 1.18/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 1.18/0.52    inference(equality_resolution,[],[f70])).
% 1.18/0.52  fof(f70,plain,(
% 1.18/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.18/0.52    inference(definition_unfolding,[],[f45,f62])).
% 1.18/0.52  fof(f62,plain,(
% 1.18/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f35,f61])).
% 1.18/0.52  fof(f61,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f38,f60])).
% 1.18/0.52  fof(f60,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f48,f59])).
% 1.18/0.52  fof(f59,plain,(
% 1.18/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f53,f58])).
% 1.18/0.52  fof(f58,plain,(
% 1.18/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f54,f57])).
% 1.18/0.52  fof(f57,plain,(
% 1.18/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f55,f56])).
% 1.18/0.52  fof(f56,plain,(
% 1.18/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f14])).
% 1.18/0.52  fof(f14,axiom,(
% 1.18/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.18/0.52  fof(f55,plain,(
% 1.18/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f13,axiom,(
% 1.18/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.18/0.52  fof(f54,plain,(
% 1.18/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f12])).
% 1.18/0.52  fof(f12,axiom,(
% 1.18/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.18/0.52  fof(f53,plain,(
% 1.18/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f11])).
% 1.18/0.52  fof(f11,axiom,(
% 1.18/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.18/0.52  fof(f48,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f10])).
% 1.18/0.52  fof(f10,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.18/0.52  fof(f38,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f9])).
% 1.18/0.52  fof(f9,axiom,(
% 1.18/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.18/0.52  fof(f35,plain,(
% 1.18/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f8])).
% 1.18/0.52  fof(f8,axiom,(
% 1.18/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.18/0.52  fof(f45,plain,(
% 1.18/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.18/0.52    inference(cnf_transformation,[],[f30])).
% 1.18/0.52  fof(f30,plain,(
% 1.18/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.18/0.52  fof(f29,plain,(
% 1.18/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.18/0.52    inference(rectify,[],[f27])).
% 1.18/0.52  fof(f27,plain,(
% 1.18/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.18/0.52    inference(nnf_transformation,[],[f7])).
% 1.18/0.52  fof(f7,axiom,(
% 1.18/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.18/0.52  fof(f213,plain,(
% 1.18/0.52    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_4),
% 1.18/0.52    inference(resolution,[],[f92,f100])).
% 1.18/0.52  fof(f100,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r2_hidden(X0,X1)) )),
% 1.18/0.52    inference(resolution,[],[f43,f66])).
% 1.18/0.52  fof(f66,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f36,f39])).
% 1.18/0.52  fof(f39,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f4])).
% 1.18/0.52  fof(f4,axiom,(
% 1.18/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.18/0.52  fof(f36,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f6])).
% 1.18/0.52  fof(f6,axiom,(
% 1.18/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.18/0.52  fof(f43,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f26])).
% 1.18/0.52  fof(f26,plain,(
% 1.18/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).
% 1.18/0.52  fof(f25,plain,(
% 1.18/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.18/0.52    inference(ennf_transformation,[],[f17])).
% 1.18/0.52  fof(f17,plain,(
% 1.18/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.18/0.52    inference(rectify,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.18/0.52  fof(f92,plain,(
% 1.18/0.52    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_4),
% 1.18/0.52    inference(avatar_component_clause,[],[f90])).
% 1.18/0.52  fof(f90,plain,(
% 1.18/0.52    spl5_4 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.18/0.52  fof(f204,plain,(
% 1.18/0.52    ~spl5_1 | spl5_2),
% 1.18/0.52    inference(avatar_contradiction_clause,[],[f203])).
% 1.18/0.52  fof(f203,plain,(
% 1.18/0.52    $false | (~spl5_1 | spl5_2)),
% 1.18/0.52    inference(subsumption_resolution,[],[f195,f174])).
% 1.18/0.52  fof(f174,plain,(
% 1.18/0.52    r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (~spl5_1 | spl5_2)),
% 1.18/0.52    inference(subsumption_resolution,[],[f173,f82])).
% 1.18/0.52  fof(f82,plain,(
% 1.18/0.52    ~r2_hidden(sK0,sK1) | spl5_2),
% 1.18/0.52    inference(avatar_component_clause,[],[f80])).
% 1.18/0.52  fof(f80,plain,(
% 1.18/0.52    spl5_2 <=> r2_hidden(sK0,sK1)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.18/0.52  fof(f173,plain,(
% 1.18/0.52    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl5_1),
% 1.18/0.52    inference(resolution,[],[f77,f49])).
% 1.18/0.52  fof(f49,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f31])).
% 1.18/0.52  fof(f31,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.18/0.52    inference(nnf_transformation,[],[f20])).
% 1.18/0.52  fof(f20,plain,(
% 1.18/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.18/0.52    inference(ennf_transformation,[],[f2])).
% 1.18/0.52  fof(f2,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.18/0.52  fof(f77,plain,(
% 1.18/0.52    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl5_1),
% 1.18/0.52    inference(avatar_component_clause,[],[f76])).
% 1.18/0.52  fof(f76,plain,(
% 1.18/0.52    spl5_1 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.18/0.52  fof(f195,plain,(
% 1.18/0.52    ~r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl5_1),
% 1.18/0.52    inference(resolution,[],[f148,f77])).
% 1.18/0.52  fof(f148,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(superposition,[],[f100,f67])).
% 1.18/0.52  fof(f67,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.18/0.52    inference(definition_unfolding,[],[f40,f39,f39])).
% 1.18/0.52  fof(f40,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f5])).
% 1.18/0.52  fof(f5,axiom,(
% 1.18/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.18/0.52  fof(f170,plain,(
% 1.18/0.52    spl5_1 | ~spl5_2 | spl5_3),
% 1.18/0.52    inference(avatar_contradiction_clause,[],[f169])).
% 1.18/0.52  fof(f169,plain,(
% 1.18/0.52    $false | (spl5_1 | ~spl5_2 | spl5_3)),
% 1.18/0.52    inference(subsumption_resolution,[],[f163,f85])).
% 1.18/0.52  fof(f85,plain,(
% 1.18/0.52    sK0 != sK2 | spl5_3),
% 1.18/0.52    inference(avatar_component_clause,[],[f84])).
% 1.18/0.52  fof(f84,plain,(
% 1.18/0.52    spl5_3 <=> sK0 = sK2),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.18/0.52  fof(f163,plain,(
% 1.18/0.52    sK0 = sK2 | (spl5_1 | ~spl5_2)),
% 1.18/0.52    inference(resolution,[],[f74,f145])).
% 1.18/0.52  fof(f145,plain,(
% 1.18/0.52    r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (spl5_1 | ~spl5_2)),
% 1.18/0.52    inference(subsumption_resolution,[],[f138,f81])).
% 1.18/0.52  fof(f81,plain,(
% 1.18/0.52    r2_hidden(sK0,sK1) | ~spl5_2),
% 1.18/0.52    inference(avatar_component_clause,[],[f80])).
% 1.18/0.52  fof(f138,plain,(
% 1.18/0.52    r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(sK0,sK1) | (spl5_1 | ~spl5_2)),
% 1.18/0.52    inference(resolution,[],[f123,f136])).
% 1.18/0.52  fof(f136,plain,(
% 1.18/0.52    r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (spl5_1 | ~spl5_2)),
% 1.18/0.52    inference(subsumption_resolution,[],[f135,f81])).
% 1.18/0.52  fof(f135,plain,(
% 1.18/0.52    r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~r2_hidden(sK0,sK1) | spl5_1),
% 1.18/0.52    inference(resolution,[],[f78,f51])).
% 1.18/0.52  fof(f51,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f31])).
% 1.18/0.52  fof(f78,plain,(
% 1.18/0.52    ~r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | spl5_1),
% 1.18/0.52    inference(avatar_component_clause,[],[f76])).
% 1.18/0.52  fof(f123,plain,(
% 1.18/0.52    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_xboole_0(X11,X10)) | r2_hidden(X9,X10) | ~r2_hidden(X9,X11)) )),
% 1.18/0.52    inference(resolution,[],[f52,f101])).
% 1.18/0.52  fof(f101,plain,(
% 1.18/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(X5,k3_xboole_0(X4,X5))) | ~r2_hidden(X3,X4)) )),
% 1.18/0.52    inference(resolution,[],[f43,f96])).
% 1.18/0.52  fof(f96,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1)) )),
% 1.18/0.52    inference(superposition,[],[f66,f37])).
% 1.18/0.52  fof(f37,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f1])).
% 1.18/0.52  fof(f1,axiom,(
% 1.18/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.18/0.52  fof(f52,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f31])).
% 1.18/0.52  fof(f74,plain,(
% 1.18/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.18/0.52    inference(equality_resolution,[],[f71])).
% 1.18/0.52  fof(f71,plain,(
% 1.18/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.18/0.52    inference(definition_unfolding,[],[f44,f62])).
% 1.18/0.52  fof(f44,plain,(
% 1.18/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.18/0.52    inference(cnf_transformation,[],[f30])).
% 1.18/0.52  fof(f94,plain,(
% 1.18/0.52    spl5_1 | spl5_2),
% 1.18/0.52    inference(avatar_split_clause,[],[f65,f80,f76])).
% 1.18/0.52  fof(f65,plain,(
% 1.18/0.52    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.18/0.52    inference(definition_unfolding,[],[f32,f39,f62])).
% 1.18/0.52  fof(f32,plain,(
% 1.18/0.52    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.18/0.52    inference(cnf_transformation,[],[f24])).
% 1.18/0.52  fof(f24,plain,(
% 1.18/0.52    (sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 1.18/0.52  fof(f23,plain,(
% 1.18/0.52    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f22,plain,(
% 1.18/0.52    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.18/0.52    inference(flattening,[],[f21])).
% 1.18/0.52  fof(f21,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.18/0.52    inference(nnf_transformation,[],[f18])).
% 1.18/0.52  % (15443)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.18/0.52  fof(f18,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.18/0.52    inference(ennf_transformation,[],[f16])).
% 1.18/0.52  fof(f16,negated_conjecture,(
% 1.18/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.18/0.52    inference(negated_conjecture,[],[f15])).
% 1.18/0.52  fof(f15,conjecture,(
% 1.18/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.18/0.52  fof(f93,plain,(
% 1.18/0.52    spl5_4 | ~spl5_3),
% 1.18/0.52    inference(avatar_split_clause,[],[f88,f84,f90])).
% 1.18/0.52  fof(f88,plain,(
% 1.18/0.52    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.18/0.52    inference(inner_rewriting,[],[f64])).
% 1.18/0.52  fof(f64,plain,(
% 1.18/0.52    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.18/0.52    inference(definition_unfolding,[],[f33,f39,f62])).
% 1.18/0.52  fof(f33,plain,(
% 1.18/0.52    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.18/0.52    inference(cnf_transformation,[],[f24])).
% 1.18/0.52  fof(f87,plain,(
% 1.18/0.52    ~spl5_1 | ~spl5_2 | spl5_3),
% 1.18/0.52    inference(avatar_split_clause,[],[f63,f84,f80,f76])).
% 1.18/0.52  fof(f63,plain,(
% 1.18/0.52    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.18/0.52    inference(definition_unfolding,[],[f34,f39,f62])).
% 1.18/0.52  fof(f34,plain,(
% 1.18/0.52    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.18/0.52    inference(cnf_transformation,[],[f24])).
% 1.18/0.52  % SZS output end Proof for theBenchmark
% 1.18/0.52  % (15430)------------------------------
% 1.18/0.52  % (15430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (15430)Termination reason: Refutation
% 1.18/0.52  
% 1.18/0.52  % (15430)Memory used [KB]: 10746
% 1.18/0.52  % (15430)Time elapsed: 0.114 s
% 1.18/0.52  % (15430)------------------------------
% 1.18/0.52  % (15430)------------------------------
% 1.29/0.53  % (15421)Success in time 0.166 s
%------------------------------------------------------------------------------
