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
% DateTime   : Thu Dec  3 12:41:15 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 254 expanded)
%              Number of leaves         :   21 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 ( 827 expanded)
%              Number of equality atoms :   97 ( 294 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f133,f493,f575,f772,f815])).

fof(f815,plain,
    ( spl4_2
    | spl4_5
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f814])).

fof(f814,plain,
    ( $false
    | spl4_2
    | spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f813,f574])).

fof(f574,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl4_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f813,plain,
    ( r2_hidden(sK0,sK1)
    | spl4_2
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f791,f793])).

fof(f793,plain,
    ( sK0 = sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f771,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f771,plain,
    ( r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f769])).

fof(f769,plain,
    ( spl4_10
  <=> r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f791,plain,
    ( r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl4_2
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f771,f132,f771,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f46,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f132,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f772,plain,
    ( spl4_10
    | spl4_2 ),
    inference(avatar_split_clause,[],[f181,f130,f769])).

fof(f181,plain,
    ( r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(factoring,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f44,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f575,plain,
    ( ~ spl4_5
    | spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f569,f490,f98,f572])).

fof(f98,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f490,plain,
    ( spl4_4
  <=> r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f569,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1
    | spl4_4 ),
    inference(backward_demodulation,[],[f492,f556])).

fof(f556,plain,
    ( sK0 = sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f81,f100,f124])).

fof(f124,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14),X14)
      | k5_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),k3_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13)) = X14
      | sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14) = X12 ) ),
    inference(resolution,[],[f65,f71])).

fof(f100,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f81,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f79,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f73,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f492,plain,
    ( ~ r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f490])).

fof(f493,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f111,f98,f490])).

fof(f111,plain,
    ( ~ r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f81,f100,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f45,f35])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f57,f130])).

fof(f57,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f29,f56,f35,f56])).

fof(f29,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f101,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f58,f98])).

fof(f58,plain,(
    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f28,f35,f56])).

fof(f28,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (805208065)
% 0.13/0.37  ipcrm: permission denied for id (804028419)
% 0.13/0.37  ipcrm: permission denied for id (805273604)
% 0.13/0.37  ipcrm: permission denied for id (805306373)
% 0.13/0.37  ipcrm: permission denied for id (805339142)
% 0.13/0.37  ipcrm: permission denied for id (804093959)
% 0.13/0.37  ipcrm: permission denied for id (805371912)
% 0.20/0.38  ipcrm: permission denied for id (805437449)
% 0.20/0.38  ipcrm: permission denied for id (805470218)
% 0.20/0.38  ipcrm: permission denied for id (805502987)
% 0.20/0.38  ipcrm: permission denied for id (805601293)
% 0.20/0.38  ipcrm: permission denied for id (805634062)
% 0.20/0.38  ipcrm: permission denied for id (804159503)
% 0.20/0.38  ipcrm: permission denied for id (805699601)
% 0.20/0.39  ipcrm: permission denied for id (805797908)
% 0.20/0.39  ipcrm: permission denied for id (805830677)
% 0.20/0.39  ipcrm: permission denied for id (805863446)
% 0.20/0.39  ipcrm: permission denied for id (804225047)
% 0.20/0.39  ipcrm: permission denied for id (804257816)
% 0.20/0.39  ipcrm: permission denied for id (804290585)
% 0.20/0.40  ipcrm: permission denied for id (805928987)
% 0.20/0.40  ipcrm: permission denied for id (804356125)
% 0.20/0.40  ipcrm: permission denied for id (804388894)
% 0.20/0.40  ipcrm: permission denied for id (805994527)
% 0.20/0.40  ipcrm: permission denied for id (806092834)
% 0.20/0.41  ipcrm: permission denied for id (806125603)
% 0.20/0.41  ipcrm: permission denied for id (806191141)
% 0.20/0.41  ipcrm: permission denied for id (806223910)
% 0.20/0.41  ipcrm: permission denied for id (804487207)
% 0.20/0.41  ipcrm: permission denied for id (806256680)
% 0.20/0.41  ipcrm: permission denied for id (804519977)
% 0.20/0.42  ipcrm: permission denied for id (804552747)
% 0.20/0.42  ipcrm: permission denied for id (806453296)
% 0.20/0.42  ipcrm: permission denied for id (806486065)
% 0.20/0.43  ipcrm: permission denied for id (804585523)
% 0.20/0.43  ipcrm: permission denied for id (806584373)
% 0.20/0.43  ipcrm: permission denied for id (804618294)
% 0.20/0.43  ipcrm: permission denied for id (804651063)
% 0.20/0.44  ipcrm: permission denied for id (806780988)
% 0.20/0.44  ipcrm: permission denied for id (806846526)
% 0.20/0.44  ipcrm: permission denied for id (806912064)
% 0.20/0.44  ipcrm: permission denied for id (806944833)
% 0.20/0.45  ipcrm: permission denied for id (807043140)
% 0.20/0.45  ipcrm: permission denied for id (807075909)
% 0.20/0.45  ipcrm: permission denied for id (807141447)
% 0.20/0.45  ipcrm: permission denied for id (804782154)
% 0.20/0.45  ipcrm: permission denied for id (807272524)
% 0.20/0.46  ipcrm: permission denied for id (807305293)
% 0.20/0.46  ipcrm: permission denied for id (807370831)
% 0.20/0.46  ipcrm: permission denied for id (807403600)
% 0.20/0.46  ipcrm: permission denied for id (807469138)
% 0.20/0.46  ipcrm: permission denied for id (807501907)
% 0.20/0.47  ipcrm: permission denied for id (807632983)
% 0.20/0.47  ipcrm: permission denied for id (807698521)
% 0.20/0.47  ipcrm: permission denied for id (807731290)
% 0.20/0.48  ipcrm: permission denied for id (807895135)
% 0.20/0.48  ipcrm: permission denied for id (807993442)
% 0.20/0.48  ipcrm: permission denied for id (808026211)
% 0.20/0.49  ipcrm: permission denied for id (808091749)
% 0.20/0.49  ipcrm: permission denied for id (808190056)
% 0.20/0.49  ipcrm: permission denied for id (808321132)
% 0.20/0.50  ipcrm: permission denied for id (808386670)
% 0.20/0.50  ipcrm: permission denied for id (808419439)
% 0.20/0.50  ipcrm: permission denied for id (808452208)
% 0.20/0.50  ipcrm: permission denied for id (805044337)
% 0.20/0.50  ipcrm: permission denied for id (808517747)
% 0.20/0.50  ipcrm: permission denied for id (808550516)
% 0.20/0.50  ipcrm: permission denied for id (808583285)
% 0.20/0.51  ipcrm: permission denied for id (805109878)
% 0.20/0.51  ipcrm: permission denied for id (808616055)
% 0.20/0.51  ipcrm: permission denied for id (808714362)
% 0.20/0.51  ipcrm: permission denied for id (808779900)
% 0.20/0.52  ipcrm: permission denied for id (808845438)
% 0.37/0.65  % (29607)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.37/0.65  % (29611)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.37/0.66  % (29606)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.37/0.67  % (29619)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.37/0.67  % (29621)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.37/0.67  % (29621)Refutation not found, incomplete strategy% (29621)------------------------------
% 0.37/0.67  % (29621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (29621)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.67  
% 0.37/0.67  % (29621)Memory used [KB]: 1663
% 0.37/0.67  % (29621)Time elapsed: 0.105 s
% 0.37/0.67  % (29621)------------------------------
% 0.37/0.67  % (29621)------------------------------
% 0.37/0.67  % (29629)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.37/0.67  % (29613)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.40/0.68  % (29624)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.40/0.68  % (29627)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.40/0.68  % (29612)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.40/0.68  % (29610)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.40/0.68  % (29615)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.40/0.68  % (29625)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.40/0.69  % (29604)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.40/0.69  % (29614)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.40/0.69  % (29608)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.40/0.69  % (29620)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.40/0.69  % (29620)Refutation not found, incomplete strategy% (29620)------------------------------
% 0.40/0.69  % (29620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.69  % (29620)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.69  
% 0.40/0.69  % (29620)Memory used [KB]: 10618
% 0.40/0.69  % (29620)Time elapsed: 0.131 s
% 0.40/0.69  % (29620)------------------------------
% 0.40/0.69  % (29620)------------------------------
% 0.40/0.70  % (29605)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.40/0.70  % (29622)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.40/0.70  % (29605)Refutation not found, incomplete strategy% (29605)------------------------------
% 0.40/0.70  % (29605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.70  % (29605)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.70  
% 0.40/0.70  % (29605)Memory used [KB]: 1663
% 0.40/0.70  % (29605)Time elapsed: 0.127 s
% 0.40/0.70  % (29605)------------------------------
% 0.40/0.70  % (29605)------------------------------
% 0.40/0.70  % (29630)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.40/0.70  % (29631)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.40/0.70  % (29622)Refutation not found, incomplete strategy% (29622)------------------------------
% 0.40/0.70  % (29622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.70  % (29633)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.40/0.70  % (29633)Refutation not found, incomplete strategy% (29633)------------------------------
% 0.40/0.70  % (29633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.70  % (29630)Refutation not found, incomplete strategy% (29630)------------------------------
% 0.40/0.70  % (29630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.70  % (29622)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.70  
% 0.40/0.70  % (29622)Memory used [KB]: 1663
% 0.40/0.70  % (29622)Time elapsed: 0.128 s
% 0.40/0.70  % (29622)------------------------------
% 0.40/0.70  % (29622)------------------------------
% 0.40/0.70  % (29623)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.40/0.70  % (29632)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.40/0.70  % (29616)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.40/0.70  % (29633)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.70  
% 0.40/0.70  % (29633)Memory used [KB]: 1663
% 0.40/0.70  % (29633)Time elapsed: 0.003 s
% 0.40/0.70  % (29633)------------------------------
% 0.40/0.70  % (29633)------------------------------
% 0.40/0.71  % (29630)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.71  
% 0.40/0.71  % (29630)Memory used [KB]: 6140
% 0.40/0.71  % (29630)Time elapsed: 0.123 s
% 0.40/0.71  % (29630)------------------------------
% 0.40/0.71  % (29630)------------------------------
% 0.40/0.71  % (29628)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.40/0.71  % (29617)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.40/0.71  % (29628)Refutation not found, incomplete strategy% (29628)------------------------------
% 0.40/0.71  % (29628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.71  % (29628)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.71  
% 0.40/0.71  % (29628)Memory used [KB]: 10618
% 0.40/0.71  % (29628)Time elapsed: 0.140 s
% 0.40/0.71  % (29628)------------------------------
% 0.40/0.71  % (29628)------------------------------
% 0.40/0.71  % (29626)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.40/0.71  % (29631)Refutation not found, incomplete strategy% (29631)------------------------------
% 0.40/0.71  % (29631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.71  % (29631)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.71  
% 0.40/0.71  % (29631)Memory used [KB]: 6140
% 0.40/0.71  % (29631)Time elapsed: 0.136 s
% 0.40/0.71  % (29631)------------------------------
% 0.40/0.71  % (29631)------------------------------
% 0.40/0.71  % (29609)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.40/0.72  % (29616)Refutation not found, incomplete strategy% (29616)------------------------------
% 0.40/0.72  % (29616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.72  % (29616)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.72  
% 0.40/0.72  % (29616)Memory used [KB]: 10618
% 0.40/0.72  % (29616)Time elapsed: 0.148 s
% 0.40/0.72  % (29616)------------------------------
% 0.40/0.72  % (29616)------------------------------
% 0.40/0.72  % (29618)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.40/0.72  % (29618)Refutation not found, incomplete strategy% (29618)------------------------------
% 0.40/0.72  % (29618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.72  % (29618)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.72  
% 0.40/0.72  % (29618)Memory used [KB]: 1663
% 0.40/0.72  % (29618)Time elapsed: 0.149 s
% 0.40/0.72  % (29618)------------------------------
% 0.40/0.72  % (29618)------------------------------
% 0.80/0.76  % (29624)Refutation found. Thanks to Tanya!
% 0.80/0.76  % SZS status Theorem for theBenchmark
% 0.80/0.77  % SZS output start Proof for theBenchmark
% 0.80/0.77  fof(f816,plain,(
% 0.80/0.77    $false),
% 0.80/0.77    inference(avatar_sat_refutation,[],[f101,f133,f493,f575,f772,f815])).
% 0.80/0.77  fof(f815,plain,(
% 0.80/0.77    spl4_2 | spl4_5 | ~spl4_10),
% 0.80/0.77    inference(avatar_contradiction_clause,[],[f814])).
% 0.80/0.77  fof(f814,plain,(
% 0.80/0.77    $false | (spl4_2 | spl4_5 | ~spl4_10)),
% 0.80/0.77    inference(subsumption_resolution,[],[f813,f574])).
% 0.80/0.77  fof(f574,plain,(
% 0.80/0.77    ~r2_hidden(sK0,sK1) | spl4_5),
% 0.80/0.77    inference(avatar_component_clause,[],[f572])).
% 0.80/0.77  fof(f572,plain,(
% 0.80/0.77    spl4_5 <=> r2_hidden(sK0,sK1)),
% 0.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.80/0.77  fof(f813,plain,(
% 0.80/0.77    r2_hidden(sK0,sK1) | (spl4_2 | ~spl4_10)),
% 0.80/0.77    inference(forward_demodulation,[],[f791,f793])).
% 0.80/0.77  fof(f793,plain,(
% 0.80/0.77    sK0 = sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_10),
% 0.80/0.77    inference(unit_resulting_resolution,[],[f771,f71])).
% 0.80/0.77  fof(f71,plain,(
% 0.80/0.77    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 0.80/0.77    inference(equality_resolution,[],[f62])).
% 0.80/0.77  fof(f62,plain,(
% 0.80/0.77    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.80/0.77    inference(definition_unfolding,[],[f36,f56])).
% 0.80/0.77  fof(f56,plain,(
% 0.80/0.77    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f32,f55])).
% 0.80/0.77  fof(f55,plain,(
% 0.80/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f34,f54])).
% 0.80/0.77  fof(f54,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f40,f53])).
% 0.80/0.77  fof(f53,plain,(
% 0.80/0.77    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f47,f52])).
% 0.80/0.77  fof(f52,plain,(
% 0.80/0.77    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f48,f51])).
% 0.80/0.77  fof(f51,plain,(
% 0.80/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f49,f50])).
% 0.80/0.77  fof(f50,plain,(
% 0.80/0.77    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f13])).
% 0.80/0.77  fof(f13,axiom,(
% 0.80/0.77    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.80/0.77  fof(f49,plain,(
% 0.80/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f12])).
% 0.80/0.77  fof(f12,axiom,(
% 0.80/0.77    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.80/0.77  fof(f48,plain,(
% 0.80/0.77    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f11])).
% 0.80/0.77  fof(f11,axiom,(
% 0.80/0.77    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.80/0.77  fof(f47,plain,(
% 0.80/0.77    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f10])).
% 0.80/0.77  fof(f10,axiom,(
% 0.80/0.77    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.80/0.77  fof(f40,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f9])).
% 0.80/0.77  fof(f9,axiom,(
% 0.80/0.77    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.80/0.77  fof(f34,plain,(
% 0.80/0.77    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f8])).
% 0.80/0.77  fof(f8,axiom,(
% 0.80/0.77    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.80/0.77  fof(f32,plain,(
% 0.80/0.77    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f7])).
% 0.80/0.77  fof(f7,axiom,(
% 0.80/0.77    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.80/0.77  fof(f36,plain,(
% 0.80/0.77    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.80/0.77    inference(cnf_transformation,[],[f22])).
% 0.80/0.77  fof(f22,plain,(
% 0.80/0.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.80/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.80/0.77  fof(f21,plain,(
% 0.80/0.77    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.80/0.77    introduced(choice_axiom,[])).
% 0.80/0.77  fof(f20,plain,(
% 0.80/0.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.80/0.77    inference(rectify,[],[f19])).
% 0.80/0.77  fof(f19,plain,(
% 0.80/0.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.80/0.77    inference(nnf_transformation,[],[f6])).
% 0.80/0.77  fof(f6,axiom,(
% 0.80/0.77    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.80/0.77  fof(f771,plain,(
% 0.80/0.77    r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_10),
% 0.80/0.77    inference(avatar_component_clause,[],[f769])).
% 0.80/0.77  fof(f769,plain,(
% 0.80/0.77    spl4_10 <=> r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.80/0.77  fof(f791,plain,(
% 0.80/0.77    r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | (spl4_2 | ~spl4_10)),
% 0.80/0.77    inference(unit_resulting_resolution,[],[f771,f132,f771,f63])).
% 0.80/0.77  fof(f63,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.80/0.77    inference(definition_unfolding,[],[f46,f35])).
% 0.80/0.77  fof(f35,plain,(
% 0.80/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.80/0.77    inference(cnf_transformation,[],[f3])).
% 0.80/0.77  fof(f3,axiom,(
% 0.80/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.80/0.77  fof(f46,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f27])).
% 0.80/0.77  fof(f27,plain,(
% 0.80/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.80/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.80/0.77  fof(f26,plain,(
% 0.80/0.77    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.80/0.77    introduced(choice_axiom,[])).
% 0.80/0.77  fof(f25,plain,(
% 0.80/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.80/0.77    inference(rectify,[],[f24])).
% 0.80/0.77  fof(f24,plain,(
% 0.80/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.80/0.77    inference(flattening,[],[f23])).
% 0.80/0.77  fof(f23,plain,(
% 0.80/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.80/0.77    inference(nnf_transformation,[],[f2])).
% 0.80/0.77  fof(f2,axiom,(
% 0.80/0.77    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.80/0.77  fof(f132,plain,(
% 0.80/0.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_2),
% 0.80/0.77    inference(avatar_component_clause,[],[f130])).
% 0.80/0.77  fof(f130,plain,(
% 0.80/0.77    spl4_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.80/0.77  fof(f772,plain,(
% 0.80/0.77    spl4_10 | spl4_2),
% 0.80/0.77    inference(avatar_split_clause,[],[f181,f130,f769])).
% 0.80/0.77  fof(f181,plain,(
% 0.80/0.77    r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl4_2),
% 0.80/0.77    inference(unit_resulting_resolution,[],[f132,f125])).
% 0.80/0.77  fof(f125,plain,(
% 0.80/0.77    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.80/0.77    inference(factoring,[],[f65])).
% 0.80/0.77  fof(f65,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.80/0.77    inference(definition_unfolding,[],[f44,f35])).
% 0.80/0.77  fof(f44,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f27])).
% 0.80/0.77  fof(f575,plain,(
% 0.80/0.77    ~spl4_5 | spl4_1 | spl4_4),
% 0.80/0.77    inference(avatar_split_clause,[],[f569,f490,f98,f572])).
% 0.80/0.77  fof(f98,plain,(
% 0.80/0.77    spl4_1 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.80/0.77  fof(f490,plain,(
% 0.80/0.77    spl4_4 <=> r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)),
% 0.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.80/0.77  fof(f569,plain,(
% 0.80/0.77    ~r2_hidden(sK0,sK1) | (spl4_1 | spl4_4)),
% 0.80/0.77    inference(backward_demodulation,[],[f492,f556])).
% 0.80/0.77  fof(f556,plain,(
% 0.80/0.77    sK0 = sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | spl4_1),
% 0.80/0.77    inference(unit_resulting_resolution,[],[f81,f100,f124])).
% 0.80/0.77  fof(f124,plain,(
% 0.80/0.77    ( ! [X14,X12,X13] : (r2_hidden(sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14),X14) | k5_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),k3_xboole_0(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13)) = X14 | sK3(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X12),X13,X14) = X12) )),
% 0.80/0.77    inference(resolution,[],[f65,f71])).
% 0.80/0.77  fof(f100,plain,(
% 0.80/0.77    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_1),
% 0.80/0.77    inference(avatar_component_clause,[],[f98])).
% 0.80/0.77  fof(f81,plain,(
% 0.80/0.77    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.80/0.77    inference(condensation,[],[f80])).
% 0.80/0.77  fof(f80,plain,(
% 0.80/0.77    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.80/0.77    inference(forward_demodulation,[],[f79,f31])).
% 0.80/0.77  fof(f31,plain,(
% 0.80/0.77    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.80/0.77    inference(cnf_transformation,[],[f5])).
% 0.80/0.77  fof(f5,axiom,(
% 0.80/0.77    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.80/0.77  fof(f79,plain,(
% 0.80/0.77    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.80/0.77    inference(superposition,[],[f73,f30])).
% 0.80/0.77  fof(f30,plain,(
% 0.80/0.77    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f4])).
% 0.80/0.77  fof(f4,axiom,(
% 0.80/0.77    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.80/0.77  fof(f73,plain,(
% 0.80/0.77    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.80/0.77    inference(equality_resolution,[],[f67])).
% 0.80/0.77  fof(f67,plain,(
% 0.80/0.77    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.80/0.77    inference(definition_unfolding,[],[f42,f35])).
% 0.80/0.77  fof(f42,plain,(
% 0.80/0.77    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.80/0.77    inference(cnf_transformation,[],[f27])).
% 0.80/0.77  fof(f492,plain,(
% 0.80/0.77    ~r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | spl4_4),
% 0.80/0.77    inference(avatar_component_clause,[],[f490])).
% 0.80/0.77  fof(f493,plain,(
% 0.80/0.77    ~spl4_4 | spl4_1),
% 0.80/0.77    inference(avatar_split_clause,[],[f111,f98,f490])).
% 0.80/0.77  fof(f111,plain,(
% 0.80/0.77    ~r2_hidden(sK3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | spl4_1),
% 0.80/0.77    inference(unit_resulting_resolution,[],[f81,f100,f64])).
% 0.80/0.77  fof(f64,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.80/0.77    inference(definition_unfolding,[],[f45,f35])).
% 0.80/0.77  fof(f45,plain,(
% 0.80/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.80/0.77    inference(cnf_transformation,[],[f27])).
% 0.80/0.77  fof(f133,plain,(
% 0.80/0.77    ~spl4_2),
% 0.80/0.77    inference(avatar_split_clause,[],[f57,f130])).
% 0.80/0.77  fof(f57,plain,(
% 0.80/0.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.80/0.77    inference(definition_unfolding,[],[f29,f56,f35,f56])).
% 0.80/0.77  fof(f29,plain,(
% 0.80/0.77    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.80/0.77    inference(cnf_transformation,[],[f18])).
% 0.80/0.77  fof(f18,plain,(
% 0.80/0.77    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.80/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.80/0.77  fof(f17,plain,(
% 0.80/0.77    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.80/0.77    introduced(choice_axiom,[])).
% 0.80/0.77  fof(f16,plain,(
% 0.80/0.77    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.80/0.77    inference(ennf_transformation,[],[f15])).
% 0.80/0.77  fof(f15,negated_conjecture,(
% 0.80/0.77    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.80/0.77    inference(negated_conjecture,[],[f14])).
% 0.80/0.77  fof(f14,conjecture,(
% 0.80/0.77    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.80/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.80/0.77  fof(f101,plain,(
% 0.80/0.77    ~spl4_1),
% 0.80/0.77    inference(avatar_split_clause,[],[f58,f98])).
% 0.80/0.77  fof(f58,plain,(
% 0.80/0.77    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.80/0.77    inference(definition_unfolding,[],[f28,f35,f56])).
% 0.80/0.77  fof(f28,plain,(
% 0.80/0.77    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.80/0.77    inference(cnf_transformation,[],[f18])).
% 0.80/0.77  % SZS output end Proof for theBenchmark
% 0.80/0.77  % (29624)------------------------------
% 0.80/0.77  % (29624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.77  % (29624)Termination reason: Refutation
% 0.80/0.77  
% 0.80/0.77  % (29624)Memory used [KB]: 11641
% 0.80/0.77  % (29624)Time elapsed: 0.191 s
% 0.80/0.77  % (29624)------------------------------
% 0.80/0.77  % (29624)------------------------------
% 0.80/0.77  % (29470)Success in time 0.407 s
%------------------------------------------------------------------------------
