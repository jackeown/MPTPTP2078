%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 2.80s
% Output     : Refutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 186 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  242 (1051 expanded)
%              Number of equality atoms :   37 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7959,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f566,f1007,f3907,f4262,f6639,f7553,f7840,f7841])).

fof(f7841,plain,
    ( spl4_18
    | spl4_19
    | spl4_17 ),
    inference(avatar_split_clause,[],[f640,f501,f575,f505])).

fof(f505,plain,
    ( spl4_18
  <=> r2_hidden(sK2(sK0,sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f575,plain,
    ( spl4_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f501,plain,
    ( spl4_17
  <=> r2_hidden(sK2(sK0,sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f640,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | r2_hidden(sK2(sK0,sK0,k1_xboole_0),sK0)
    | spl4_17 ),
    inference(resolution,[],[f502,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f502,plain,
    ( ~ r2_hidden(sK2(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f501])).

fof(f7840,plain,
    ( ~ spl4_18
    | spl4_19
    | spl4_17 ),
    inference(avatar_split_clause,[],[f641,f501,f575,f505])).

fof(f641,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ r2_hidden(sK2(sK0,sK0,k1_xboole_0),sK0)
    | spl4_17 ),
    inference(resolution,[],[f502,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7553,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f7552])).

fof(f7552,plain,
    ( $false
    | spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f7551,f6794])).

fof(f6794,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(subsumption_resolution,[],[f6785,f36])).

fof(f36,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f6785,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(resolution,[],[f172,f52])).

fof(f172,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_9
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f7551,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f7533,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f7533,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl4_9
    | ~ spl4_10 ),
    inference(resolution,[],[f6787,f177])).

fof(f177,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_10
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f6787,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) )
    | spl4_9 ),
    inference(resolution,[],[f172,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6639,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f6638])).

fof(f6638,plain,
    ( $false
    | ~ spl4_9
    | spl4_10
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f6637,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f6637,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_9
    | spl4_10
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f6629,f661])).

fof(f661,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_xboole_0)
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f629,f628])).

fof(f628,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | ~ r2_hidden(X5,sK0) )
    | ~ spl4_19 ),
    inference(superposition,[],[f64,f577])).

fof(f577,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f575])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f629,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | r2_hidden(X6,sK0) )
    | ~ spl4_19 ),
    inference(superposition,[],[f65,f577])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6629,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_9
    | spl4_10 ),
    inference(superposition,[],[f2856,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2856,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ spl4_9
    | spl4_10 ),
    inference(resolution,[],[f914,f173])).

fof(f173,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f914,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0)) )
    | spl4_10 ),
    inference(resolution,[],[f176,f63])).

fof(f176,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f4262,plain,
    ( ~ spl4_9
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f4261])).

fof(f4261,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4253,f888])).

fof(f888,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f886])).

fof(f886,plain,
    ( spl4_20
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f4253,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl4_9 ),
    inference(superposition,[],[f876,f39])).

fof(f876,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_9 ),
    inference(resolution,[],[f173,f64])).

fof(f3907,plain,
    ( ~ spl4_9
    | spl4_20
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f3906,f175,f886,f171])).

fof(f3906,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f3881,f36])).

fof(f3881,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f177,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1007,plain,
    ( spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f1006,f175,f171])).

fof(f1006,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f36,f51])).

fof(f566,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl4_17 ),
    inference(resolution,[],[f557,f503])).

fof(f503,plain,
    ( r2_hidden(sK2(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f501])).

fof(f557,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,sK0,k1_xboole_0),X2)
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f555,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f555,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,sK0,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))
    | ~ spl4_17 ),
    inference(resolution,[],[f503,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n002.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:49:51 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.43  % (9273)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.44  % (9268)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.44  % (9265)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.44  % (9273)Refutation not found, incomplete strategy% (9273)------------------------------
% 0.18/0.44  % (9273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (9273)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.44  
% 0.18/0.44  % (9273)Memory used [KB]: 6012
% 0.18/0.44  % (9273)Time elapsed: 0.054 s
% 0.18/0.44  % (9273)------------------------------
% 0.18/0.44  % (9273)------------------------------
% 0.18/0.45  % (9276)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.45  % (9276)Refutation not found, incomplete strategy% (9276)------------------------------
% 0.18/0.45  % (9276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (9276)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.45  
% 0.18/0.45  % (9276)Memory used [KB]: 1663
% 0.18/0.45  % (9276)Time elapsed: 0.061 s
% 0.18/0.45  % (9276)------------------------------
% 0.18/0.45  % (9276)------------------------------
% 0.18/0.46  % (9271)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.47  % (9278)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.47  % (9278)Refutation not found, incomplete strategy% (9278)------------------------------
% 0.18/0.47  % (9278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (9278)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (9278)Memory used [KB]: 6140
% 0.18/0.47  % (9278)Time elapsed: 0.003 s
% 0.18/0.47  % (9278)------------------------------
% 0.18/0.47  % (9278)------------------------------
% 0.18/0.47  % (9266)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.47  % (9267)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.47  % (9270)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.47  % (9269)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.48  % (9280)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.18/0.48  % (9282)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.48  % (9264)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (9283)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.48  % (9264)Refutation not found, incomplete strategy% (9264)------------------------------
% 0.18/0.48  % (9264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (9264)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (9264)Memory used [KB]: 10618
% 0.18/0.48  % (9264)Time elapsed: 0.092 s
% 0.18/0.48  % (9264)------------------------------
% 0.18/0.48  % (9264)------------------------------
% 0.18/0.48  % (9283)Refutation not found, incomplete strategy% (9283)------------------------------
% 0.18/0.48  % (9283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (9283)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (9283)Memory used [KB]: 10618
% 0.18/0.48  % (9283)Time elapsed: 0.093 s
% 0.18/0.48  % (9283)------------------------------
% 0.18/0.48  % (9283)------------------------------
% 0.18/0.48  % (9266)Refutation not found, incomplete strategy% (9266)------------------------------
% 0.18/0.48  % (9266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (9266)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (9266)Memory used [KB]: 10618
% 0.18/0.48  % (9266)Time elapsed: 0.093 s
% 0.18/0.48  % (9266)------------------------------
% 0.18/0.48  % (9266)------------------------------
% 0.18/0.48  % (9281)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.48  % (9272)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.18/0.49  % (9274)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.49  % (9263)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.49  % (9275)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.49  % (9263)Refutation not found, incomplete strategy% (9263)------------------------------
% 0.18/0.49  % (9263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (9263)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (9263)Memory used [KB]: 6140
% 0.18/0.49  % (9263)Time elapsed: 0.101 s
% 0.18/0.49  % (9263)------------------------------
% 0.18/0.49  % (9263)------------------------------
% 0.18/0.49  % (9275)Refutation not found, incomplete strategy% (9275)------------------------------
% 0.18/0.49  % (9275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (9275)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (9275)Memory used [KB]: 6012
% 0.18/0.49  % (9275)Time elapsed: 0.001 s
% 0.18/0.49  % (9275)------------------------------
% 0.18/0.49  % (9275)------------------------------
% 0.18/0.49  % (9274)Refutation not found, incomplete strategy% (9274)------------------------------
% 0.18/0.49  % (9274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (9274)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (9274)Memory used [KB]: 10618
% 0.18/0.49  % (9274)Time elapsed: 0.106 s
% 0.18/0.49  % (9274)------------------------------
% 0.18/0.49  % (9274)------------------------------
% 0.18/0.49  % (9277)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.49  % (9279)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 2.80/0.72  % (9282)Refutation found. Thanks to Tanya!
% 2.80/0.72  % SZS status Theorem for theBenchmark
% 2.80/0.74  % SZS output start Proof for theBenchmark
% 2.80/0.74  fof(f7959,plain,(
% 2.80/0.74    $false),
% 2.80/0.74    inference(avatar_sat_refutation,[],[f566,f1007,f3907,f4262,f6639,f7553,f7840,f7841])).
% 2.80/0.74  fof(f7841,plain,(
% 2.80/0.74    spl4_18 | spl4_19 | spl4_17),
% 2.80/0.74    inference(avatar_split_clause,[],[f640,f501,f575,f505])).
% 2.80/0.74  fof(f505,plain,(
% 2.80/0.74    spl4_18 <=> r2_hidden(sK2(sK0,sK0,k1_xboole_0),sK0)),
% 2.80/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.80/0.74  fof(f575,plain,(
% 2.80/0.74    spl4_19 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 2.80/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.80/0.74  fof(f501,plain,(
% 2.80/0.74    spl4_17 <=> r2_hidden(sK2(sK0,sK0,k1_xboole_0),k1_xboole_0)),
% 2.80/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.80/0.74  fof(f640,plain,(
% 2.80/0.74    k1_xboole_0 = k4_xboole_0(sK0,sK0) | r2_hidden(sK2(sK0,sK0,k1_xboole_0),sK0) | spl4_17),
% 2.80/0.74    inference(resolution,[],[f502,f51])).
% 2.80/0.74  fof(f51,plain,(
% 2.80/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.80/0.74    inference(cnf_transformation,[],[f31])).
% 2.80/0.74  fof(f31,plain,(
% 2.80/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.80/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 2.80/0.74  fof(f30,plain,(
% 2.80/0.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.80/0.74    introduced(choice_axiom,[])).
% 2.80/0.74  fof(f29,plain,(
% 2.80/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.80/0.74    inference(rectify,[],[f28])).
% 2.80/0.74  fof(f28,plain,(
% 2.80/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.80/0.74    inference(flattening,[],[f27])).
% 2.80/0.74  fof(f27,plain,(
% 2.80/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.80/0.74    inference(nnf_transformation,[],[f3])).
% 2.80/0.74  fof(f3,axiom,(
% 2.80/0.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.80/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.80/0.74  fof(f502,plain,(
% 2.80/0.74    ~r2_hidden(sK2(sK0,sK0,k1_xboole_0),k1_xboole_0) | spl4_17),
% 2.80/0.74    inference(avatar_component_clause,[],[f501])).
% 2.80/0.74  fof(f7840,plain,(
% 2.80/0.74    ~spl4_18 | spl4_19 | spl4_17),
% 2.80/0.74    inference(avatar_split_clause,[],[f641,f501,f575,f505])).
% 2.80/0.74  fof(f641,plain,(
% 2.80/0.74    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~r2_hidden(sK2(sK0,sK0,k1_xboole_0),sK0) | spl4_17),
% 2.80/0.74    inference(resolution,[],[f502,f52])).
% 2.80/0.74  fof(f52,plain,(
% 2.80/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.80/0.74    inference(cnf_transformation,[],[f31])).
% 2.80/0.74  fof(f7553,plain,(
% 2.80/0.74    spl4_9 | ~spl4_10),
% 2.80/0.74    inference(avatar_contradiction_clause,[],[f7552])).
% 2.80/0.74  fof(f7552,plain,(
% 2.80/0.74    $false | (spl4_9 | ~spl4_10)),
% 2.80/0.74    inference(subsumption_resolution,[],[f7551,f6794])).
% 2.80/0.74  fof(f6794,plain,(
% 2.80/0.74    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_9),
% 2.80/0.74    inference(subsumption_resolution,[],[f6785,f36])).
% 2.80/0.74  fof(f36,plain,(
% 2.80/0.74    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.80/0.74    inference(cnf_transformation,[],[f26])).
% 2.80/0.74  fof(f26,plain,(
% 2.80/0.74    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.80/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 2.80/0.74  fof(f25,plain,(
% 2.80/0.74    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.80/0.74    introduced(choice_axiom,[])).
% 2.80/0.74  fof(f22,plain,(
% 2.80/0.74    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.80/0.74    inference(ennf_transformation,[],[f19])).
% 2.80/0.74  fof(f19,negated_conjecture,(
% 2.80/0.74    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.80/0.74    inference(negated_conjecture,[],[f18])).
% 2.80/0.74  fof(f18,conjecture,(
% 2.80/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.80/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.80/0.74  fof(f6785,plain,(
% 2.80/0.74    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_9),
% 2.80/0.74    inference(resolution,[],[f172,f52])).
% 2.80/0.74  fof(f172,plain,(
% 2.80/0.74    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl4_9),
% 2.80/0.74    inference(avatar_component_clause,[],[f171])).
% 2.80/0.74  fof(f171,plain,(
% 2.80/0.74    spl4_9 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.80/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.80/0.74  fof(f7551,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl4_9 | ~spl4_10)),
% 2.80/0.74    inference(forward_demodulation,[],[f7533,f39])).
% 2.80/0.74  fof(f39,plain,(
% 2.80/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.80/0.74    inference(cnf_transformation,[],[f17])).
% 2.80/0.74  fof(f17,axiom,(
% 2.80/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.80/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.80/0.74  fof(f7533,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl4_9 | ~spl4_10)),
% 2.80/0.74    inference(resolution,[],[f6787,f177])).
% 2.80/0.74  fof(f177,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl4_10),
% 2.80/0.74    inference(avatar_component_clause,[],[f175])).
% 2.80/0.74  fof(f175,plain,(
% 2.80/0.74    spl4_10 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.80/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.80/0.74  fof(f6787,plain,(
% 2.80/0.74    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | spl4_9),
% 2.80/0.74    inference(resolution,[],[f172,f63])).
% 2.80/0.74  fof(f63,plain,(
% 2.80/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.80/0.74    inference(equality_resolution,[],[f50])).
% 2.80/0.74  fof(f50,plain,(
% 2.80/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.80/0.74    inference(cnf_transformation,[],[f31])).
% 2.80/0.74  fof(f6639,plain,(
% 2.80/0.74    ~spl4_9 | spl4_10 | ~spl4_19),
% 2.80/0.74    inference(avatar_contradiction_clause,[],[f6638])).
% 2.80/0.74  fof(f6638,plain,(
% 2.80/0.74    $false | (~spl4_9 | spl4_10 | ~spl4_19)),
% 2.80/0.74    inference(subsumption_resolution,[],[f6637,f59])).
% 2.80/0.74  fof(f59,plain,(
% 2.80/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.80/0.74    inference(cnf_transformation,[],[f9])).
% 2.80/0.74  fof(f9,axiom,(
% 2.80/0.74    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.80/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.80/0.74  fof(f6637,plain,(
% 2.80/0.74    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_9 | spl4_10 | ~spl4_19)),
% 2.80/0.74    inference(subsumption_resolution,[],[f6629,f661])).
% 2.80/0.74  fof(f661,plain,(
% 2.80/0.74    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) ) | ~spl4_19),
% 2.80/0.74    inference(subsumption_resolution,[],[f629,f628])).
% 2.80/0.74  fof(f628,plain,(
% 2.80/0.74    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,sK0)) ) | ~spl4_19),
% 2.80/0.74    inference(superposition,[],[f64,f577])).
% 2.80/0.74  fof(f577,plain,(
% 2.80/0.74    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl4_19),
% 2.80/0.74    inference(avatar_component_clause,[],[f575])).
% 2.80/0.74  fof(f64,plain,(
% 2.80/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.80/0.74    inference(equality_resolution,[],[f49])).
% 2.80/0.74  fof(f49,plain,(
% 2.80/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.80/0.74    inference(cnf_transformation,[],[f31])).
% 2.80/0.74  fof(f629,plain,(
% 2.80/0.74    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(X6,sK0)) ) | ~spl4_19),
% 2.80/0.74    inference(superposition,[],[f65,f577])).
% 2.80/0.74  fof(f65,plain,(
% 2.80/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.80/0.74    inference(equality_resolution,[],[f48])).
% 2.80/0.74  fof(f48,plain,(
% 2.80/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.80/0.74    inference(cnf_transformation,[],[f31])).
% 2.80/0.74  fof(f6629,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_9 | spl4_10)),
% 2.80/0.74    inference(superposition,[],[f2856,f55])).
% 2.80/0.74  fof(f55,plain,(
% 2.80/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.80/0.74    inference(cnf_transformation,[],[f32])).
% 2.80/0.74  fof(f32,plain,(
% 2.80/0.74    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.80/0.74    inference(nnf_transformation,[],[f7])).
% 2.80/0.74  fof(f7,axiom,(
% 2.80/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.80/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.80/0.74  fof(f2856,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl4_9 | spl4_10)),
% 2.80/0.74    inference(resolution,[],[f914,f173])).
% 2.80/0.74  fof(f173,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl4_9),
% 2.80/0.74    inference(avatar_component_clause,[],[f171])).
% 2.80/0.74  fof(f914,plain,(
% 2.80/0.74    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))) ) | spl4_10),
% 2.80/0.74    inference(resolution,[],[f176,f63])).
% 2.80/0.74  fof(f176,plain,(
% 2.80/0.74    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl4_10),
% 2.80/0.74    inference(avatar_component_clause,[],[f175])).
% 2.80/0.74  fof(f4262,plain,(
% 2.80/0.74    ~spl4_9 | ~spl4_20),
% 2.80/0.74    inference(avatar_contradiction_clause,[],[f4261])).
% 2.80/0.74  fof(f4261,plain,(
% 2.80/0.74    $false | (~spl4_9 | ~spl4_20)),
% 2.80/0.74    inference(subsumption_resolution,[],[f4253,f888])).
% 2.80/0.74  fof(f888,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl4_20),
% 2.80/0.74    inference(avatar_component_clause,[],[f886])).
% 2.80/0.74  fof(f886,plain,(
% 2.80/0.74    spl4_20 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.80/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.80/0.74  fof(f4253,plain,(
% 2.80/0.74    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl4_9),
% 2.80/0.74    inference(superposition,[],[f876,f39])).
% 2.80/0.74  fof(f876,plain,(
% 2.80/0.74    ( ! [X2] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))) ) | ~spl4_9),
% 2.80/0.74    inference(resolution,[],[f173,f64])).
% 2.80/0.74  fof(f3907,plain,(
% 2.80/0.74    ~spl4_9 | spl4_20 | ~spl4_10),
% 2.80/0.74    inference(avatar_split_clause,[],[f3906,f175,f886,f171])).
% 2.80/0.74  fof(f3906,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl4_10),
% 2.80/0.74    inference(subsumption_resolution,[],[f3881,f36])).
% 2.80/0.74  fof(f3881,plain,(
% 2.80/0.74    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl4_10),
% 2.80/0.74    inference(resolution,[],[f177,f53])).
% 2.80/0.74  fof(f53,plain,(
% 2.80/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.80/0.74    inference(cnf_transformation,[],[f31])).
% 2.80/0.74  fof(f1007,plain,(
% 2.80/0.74    spl4_9 | spl4_10),
% 2.80/0.74    inference(avatar_split_clause,[],[f1006,f175,f171])).
% 2.80/0.74  fof(f1006,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.80/0.74    inference(equality_resolution,[],[f71])).
% 2.80/0.74  fof(f71,plain,(
% 2.80/0.74    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.80/0.74    inference(superposition,[],[f36,f51])).
% 2.80/0.74  fof(f566,plain,(
% 2.80/0.74    ~spl4_17),
% 2.80/0.74    inference(avatar_contradiction_clause,[],[f558])).
% 2.80/0.74  fof(f558,plain,(
% 2.80/0.74    $false | ~spl4_17),
% 2.80/0.74    inference(resolution,[],[f557,f503])).
% 2.80/0.74  fof(f503,plain,(
% 2.80/0.74    r2_hidden(sK2(sK0,sK0,k1_xboole_0),k1_xboole_0) | ~spl4_17),
% 2.80/0.74    inference(avatar_component_clause,[],[f501])).
% 2.80/0.74  fof(f557,plain,(
% 2.80/0.74    ( ! [X2] : (~r2_hidden(sK2(sK0,sK0,k1_xboole_0),X2)) ) | ~spl4_17),
% 2.80/0.74    inference(forward_demodulation,[],[f555,f46])).
% 2.80/0.74  fof(f46,plain,(
% 2.80/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.80/0.74    inference(cnf_transformation,[],[f15])).
% 2.80/0.74  fof(f15,axiom,(
% 2.80/0.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.80/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.80/0.74  fof(f555,plain,(
% 2.80/0.74    ( ! [X2] : (~r2_hidden(sK2(sK0,sK0,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))) ) | ~spl4_17),
% 2.80/0.74    inference(resolution,[],[f503,f64])).
% 2.80/0.74  % SZS output end Proof for theBenchmark
% 2.80/0.74  % (9282)------------------------------
% 2.80/0.74  % (9282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.74  % (9282)Termination reason: Refutation
% 2.80/0.74  
% 2.80/0.74  % (9282)Memory used [KB]: 9210
% 2.80/0.74  % (9282)Time elapsed: 0.323 s
% 2.80/0.74  % (9282)------------------------------
% 2.80/0.74  % (9282)------------------------------
% 2.80/0.74  % (9262)Success in time 0.407 s
%------------------------------------------------------------------------------
