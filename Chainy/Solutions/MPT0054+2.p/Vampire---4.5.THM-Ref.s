%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0054+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 181 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  262 (1080 expanded)
%              Number of equality atoms :   34 ( 165 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2023,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f588,f1834,f1856,f2022])).

fof(f2022,plain,
    ( ~ spl18_1
    | ~ spl18_2 ),
    inference(avatar_contradiction_clause,[],[f2021])).

fof(f2021,plain,
    ( $false
    | ~ spl18_1
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f2020,f434])).

fof(f434,plain,(
    r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f423,f345])).

fof(f345,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f309])).

fof(f309,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK12(X0,X1,X2),X1)
            | ~ r2_hidden(sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK12(X0,X1,X2),X0) )
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f190,f191])).

fof(f191,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK12(X0,X1,X2),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
            & r2_hidden(sK12(X0,X1,X2),X0) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f190,plain,(
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
    inference(rectify,[],[f189])).

fof(f189,plain,(
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
    inference(flattening,[],[f188])).

fof(f188,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f423,plain,
    ( r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0)
    | r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f355,f413])).

fof(f413,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK12(X0,X1,X2),X0)
      | r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f312,f352])).

fof(f352,plain,(
    ! [X1,X0] :
      ( sQ17_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK12(X0,X1,X2),X0)
      | r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f355,plain,(
    ~ sQ17_eqProxy(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f208,f352])).

fof(f208,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f101,f153])).

fof(f153,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f85])).

fof(f85,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f84])).

fof(f84,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2020,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_1
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f2006,f441])).

fof(f441,plain,
    ( r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl18_2
  <=> r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f2006,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_1 ),
    inference(resolution,[],[f1864,f346])).

fof(f346,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f317])).

fof(f317,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f195,f196])).

fof(f196,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f195,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f194])).

fof(f194,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f193])).

fof(f193,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1864,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl18_1 ),
    inference(resolution,[],[f438,f344])).

fof(f344,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f310])).

fof(f310,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f192])).

fof(f438,plain,
    ( r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl18_1
  <=> r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f1856,plain,
    ( spl18_1
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1855,f440,f436])).

fof(f1855,plain,
    ( r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f1835,f355])).

fof(f1835,plain,
    ( sQ17_eqProxy(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(resolution,[],[f441,f412])).

fof(f412,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f313,f352])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f1834,plain,
    ( spl18_1
    | spl18_2 ),
    inference(avatar_contradiction_clause,[],[f1833])).

fof(f1833,plain,
    ( $false
    | spl18_1
    | spl18_2 ),
    inference(subsumption_resolution,[],[f712,f582])).

fof(f582,plain,
    ( ! [X9] : ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(X9,sK1))
    | spl18_2 ),
    inference(resolution,[],[f442,f347])).

fof(f347,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f316])).

fof(f316,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f197])).

fof(f442,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK1)
    | spl18_2 ),
    inference(avatar_component_clause,[],[f440])).

fof(f712,plain,
    ( r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | spl18_1 ),
    inference(subsumption_resolution,[],[f696,f434])).

fof(f696,plain,
    ( r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0)
    | spl18_1 ),
    inference(resolution,[],[f437,f343])).

fof(f343,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f311])).

fof(f311,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f192])).

fof(f437,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl18_1 ),
    inference(avatar_component_clause,[],[f436])).

fof(f588,plain,
    ( ~ spl18_1
    | spl18_2 ),
    inference(avatar_split_clause,[],[f587,f440,f436])).

fof(f587,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(subsumption_resolution,[],[f586,f434])).

fof(f586,plain,
    ( ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(subsumption_resolution,[],[f572,f355])).

fof(f572,plain,
    ( sQ17_eqProxy(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK12(sK0,sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(resolution,[],[f442,f411])).

fof(f411,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK12(X0,X1,X2),X1)
      | ~ r2_hidden(sK12(X0,X1,X2),X0)
      | ~ r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f314,f352])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK12(X0,X1,X2),X1)
      | ~ r2_hidden(sK12(X0,X1,X2),X0)
      | ~ r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f192])).
%------------------------------------------------------------------------------
