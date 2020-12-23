%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0119+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:10 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 298 expanded)
%              Number of leaves         :   15 ( 107 expanded)
%              Depth                    :   10
%              Number of atoms          :  392 (1453 expanded)
%              Number of equality atoms :   28 ( 156 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3069,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1692,f2687,f2714,f2719,f2824,f2830,f2831,f2853,f2884,f2885,f2904,f2980,f2999,f3002,f3027,f3066])).

fof(f3066,plain,
    ( spl20_30
    | ~ spl20_32
    | spl20_116 ),
    inference(avatar_contradiction_clause,[],[f3065])).

fof(f3065,plain,
    ( $false
    | spl20_30
    | ~ spl20_32
    | spl20_116 ),
    inference(subsumption_resolution,[],[f3064,f2852])).

fof(f2852,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | spl20_116 ),
    inference(avatar_component_clause,[],[f2850])).

fof(f2850,plain,
    ( spl20_116
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_116])])).

fof(f3064,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | spl20_30
    | ~ spl20_32 ),
    inference(subsumption_resolution,[],[f3043,f1006])).

fof(f1006,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | spl20_30 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1004,plain,
    ( spl20_30
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_30])])).

fof(f3043,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | ~ spl20_32 ),
    inference(resolution,[],[f1033,f537])).

fof(f537,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f334])).

fof(f334,plain,(
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
    inference(nnf_transformation,[],[f264])).

fof(f264,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1033,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,sK2))
    | ~ spl20_32 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl20_32
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_32])])).

fof(f3027,plain,
    ( spl20_32
    | ~ spl20_1 ),
    inference(avatar_split_clause,[],[f3005,f696,f1032])).

fof(f696,plain,
    ( spl20_1
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f3005,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,sK2))
    | ~ spl20_1 ),
    inference(resolution,[],[f697,f565])).

fof(f565,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f519])).

fof(f519,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f323])).

fof(f323,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f321,f322])).

fof(f322,plain,(
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

fof(f321,plain,(
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
    inference(rectify,[],[f320])).

fof(f320,plain,(
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
    inference(flattening,[],[f319])).

fof(f319,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f697,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ spl20_1 ),
    inference(avatar_component_clause,[],[f696])).

fof(f3002,plain,
    ( spl20_1
    | spl20_2
    | spl20_3 ),
    inference(avatar_split_clause,[],[f3001,f704,f700,f696])).

fof(f700,plain,
    ( spl20_2
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_2])])).

fof(f704,plain,
    ( spl20_3
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f3001,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | spl20_2
    | spl20_3 ),
    inference(subsumption_resolution,[],[f3000,f702])).

fof(f702,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | spl20_2 ),
    inference(avatar_component_clause,[],[f700])).

fof(f3000,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | spl20_3 ),
    inference(subsumption_resolution,[],[f2997,f580])).

fof(f580,plain,(
    ~ sQ19_eqProxy(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    inference(equality_proxy_replacement,[],[f341,f574])).

fof(f574,plain,(
    ! [X1,X0] :
      ( sQ19_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ19_eqProxy])])).

fof(f341,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f280])).

fof(f280,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f175,f279])).

fof(f279,plain,
    ( ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1)
   => k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f175,plain,(
    ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,negated_conjecture,(
    ~ ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f61])).

fof(f61,conjecture,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f2997,plain,
    ( sQ19_eqProxy(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | spl20_3 ),
    inference(resolution,[],[f705,f664])).

fof(f664,plain,(
    ! [X2,X0,X1] :
      ( sQ19_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f517,f574])).

fof(f517,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK12(X0,X1,X2),X2)
      | r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f318])).

fof(f318,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ( ( ( ( ~ r2_hidden(sK12(X0,X1,X2),X2)
              | ~ r2_hidden(sK12(X0,X1,X2),X1) )
            & ( r2_hidden(sK12(X0,X1,X2),X2)
              | r2_hidden(sK12(X0,X1,X2),X1) ) )
          | r2_hidden(sK12(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK12(X0,X1,X2),X1)
              | ~ r2_hidden(sK12(X0,X1,X2),X2) )
            & ( r2_hidden(sK12(X0,X1,X2),X2)
              | ~ r2_hidden(sK12(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK12(X0,X1,X2),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f316,f317])).

fof(f317,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) )
     => ( ( ( ( ~ r2_hidden(sK12(X0,X1,X2),X2)
              | ~ r2_hidden(sK12(X0,X1,X2),X1) )
            & ( r2_hidden(sK12(X0,X1,X2),X2)
              | r2_hidden(sK12(X0,X1,X2),X1) ) )
          | r2_hidden(sK12(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK12(X0,X1,X2),X1)
              | ~ r2_hidden(sK12(X0,X1,X2),X2) )
            & ( r2_hidden(sK12(X0,X1,X2),X2)
              | ~ r2_hidden(sK12(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK12(X0,X1,X2),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f316,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f263])).

fof(f263,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r2_hidden(X3,X0)
        <~> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f705,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1))
    | spl20_3 ),
    inference(avatar_component_clause,[],[f704])).

fof(f2999,plain,
    ( ~ spl20_30
    | spl20_3
    | ~ spl20_31 ),
    inference(avatar_split_clause,[],[f2998,f1008,f704,f1004])).

fof(f1008,plain,
    ( spl20_31
  <=> r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_31])])).

fof(f2998,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | spl20_3
    | ~ spl20_31 ),
    inference(subsumption_resolution,[],[f2982,f1009])).

fof(f1009,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ spl20_31 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f2982,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | spl20_3 ),
    inference(resolution,[],[f705,f563])).

fof(f563,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f521])).

fof(f521,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f323])).

fof(f2980,plain,
    ( ~ spl20_30
    | spl20_32
    | spl20_116 ),
    inference(avatar_contradiction_clause,[],[f2979])).

fof(f2979,plain,
    ( $false
    | ~ spl20_30
    | spl20_32
    | spl20_116 ),
    inference(subsumption_resolution,[],[f2978,f1005])).

fof(f1005,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | ~ spl20_30 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f2978,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | spl20_32
    | spl20_116 ),
    inference(subsumption_resolution,[],[f2964,f2852])).

fof(f2964,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | spl20_32 ),
    inference(resolution,[],[f1034,f540])).

fof(f540,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f334])).

fof(f1034,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,sK2))
    | spl20_32 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f2904,plain,
    ( ~ spl20_32
    | ~ spl20_31
    | spl20_1 ),
    inference(avatar_split_clause,[],[f2888,f696,f1008,f1032])).

fof(f2888,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,sK2))
    | spl20_1 ),
    inference(resolution,[],[f698,f563])).

fof(f698,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | spl20_1 ),
    inference(avatar_component_clause,[],[f696])).

fof(f2885,plain,
    ( spl20_31
    | ~ spl20_3 ),
    inference(avatar_split_clause,[],[f2861,f704,f1008])).

fof(f2861,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ spl20_3 ),
    inference(resolution,[],[f706,f564])).

fof(f564,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f520])).

fof(f520,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f323])).

fof(f706,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1))
    | ~ spl20_3 ),
    inference(avatar_component_clause,[],[f704])).

fof(f2884,plain,
    ( ~ spl20_1
    | spl20_2
    | ~ spl20_3 ),
    inference(avatar_split_clause,[],[f2883,f704,f700,f696])).

fof(f2883,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | spl20_2
    | ~ spl20_3 ),
    inference(subsumption_resolution,[],[f2882,f702])).

fof(f2882,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ spl20_3 ),
    inference(subsumption_resolution,[],[f2858,f580])).

fof(f2858,plain,
    ( sQ19_eqProxy(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ spl20_3 ),
    inference(resolution,[],[f706,f665])).

fof(f665,plain,(
    ! [X2,X0,X1] :
      ( sQ19_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK12(X0,X1,X2),X1)
      | ~ r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f516,f574])).

fof(f516,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK12(X0,X1,X2),X1)
      | ~ r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f318])).

fof(f2853,plain,
    ( ~ spl20_116
    | ~ spl20_31
    | spl20_2 ),
    inference(avatar_split_clause,[],[f2833,f700,f1008,f2850])).

fof(f2833,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | spl20_2 ),
    inference(resolution,[],[f702,f563])).

fof(f2831,plain,
    ( spl20_31
    | ~ spl20_1 ),
    inference(avatar_split_clause,[],[f2723,f696,f1008])).

fof(f2723,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ spl20_1 ),
    inference(resolution,[],[f697,f564])).

fof(f2830,plain,
    ( ~ spl20_2
    | spl20_3
    | ~ spl20_1 ),
    inference(avatar_split_clause,[],[f2829,f696,f704,f700])).

fof(f2829,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1))
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl20_1 ),
    inference(subsumption_resolution,[],[f2720,f580])).

fof(f2720,plain,
    ( sQ19_eqProxy(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1))
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl20_1 ),
    inference(resolution,[],[f697,f666])).

fof(f666,plain,(
    ! [X2,X0,X1] :
      ( sQ19_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | ~ r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f515,f574])).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | ~ r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f318])).

fof(f2824,plain,
    ( ~ spl20_2
    | ~ spl20_30
    | ~ spl20_32 ),
    inference(avatar_contradiction_clause,[],[f2823])).

fof(f2823,plain,
    ( $false
    | ~ spl20_2
    | ~ spl20_30
    | ~ spl20_32 ),
    inference(subsumption_resolution,[],[f2822,f945])).

fof(f945,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | ~ spl20_2 ),
    inference(resolution,[],[f701,f565])).

fof(f701,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl20_2 ),
    inference(avatar_component_clause,[],[f700])).

fof(f2822,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | ~ spl20_30
    | ~ spl20_32 ),
    inference(subsumption_resolution,[],[f2802,f1005])).

fof(f2802,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | ~ spl20_32 ),
    inference(resolution,[],[f1033,f538])).

fof(f538,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f334])).

fof(f2719,plain,
    ( spl20_30
    | ~ spl20_3 ),
    inference(avatar_split_clause,[],[f2690,f704,f1004])).

fof(f2690,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | ~ spl20_3 ),
    inference(resolution,[],[f706,f565])).

fof(f2714,plain,
    ( spl20_1
    | ~ spl20_2
    | ~ spl20_3 ),
    inference(avatar_split_clause,[],[f2713,f704,f700,f696])).

fof(f2713,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ spl20_2
    | ~ spl20_3 ),
    inference(subsumption_resolution,[],[f2712,f701])).

fof(f2712,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ spl20_3 ),
    inference(subsumption_resolution,[],[f2689,f580])).

fof(f2689,plain,
    ( sQ19_eqProxy(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1))
    | ~ spl20_3 ),
    inference(resolution,[],[f706,f663])).

fof(f663,plain,(
    ! [X2,X0,X1] :
      ( sQ19_eqProxy(k5_xboole_0(X1,X2),X0)
      | ~ r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f518,f574])).

fof(f518,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | ~ r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f318])).

fof(f2687,plain,
    ( ~ spl20_2
    | spl20_30
    | spl20_32 ),
    inference(avatar_contradiction_clause,[],[f2686])).

fof(f2686,plain,
    ( $false
    | ~ spl20_2
    | spl20_30
    | spl20_32 ),
    inference(subsumption_resolution,[],[f2685,f945])).

fof(f2685,plain,
    ( ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | spl20_30
    | spl20_32 ),
    inference(subsumption_resolution,[],[f2670,f1006])).

fof(f2670,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK2)
    | ~ r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK0)
    | spl20_32 ),
    inference(resolution,[],[f1034,f539])).

fof(f539,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f334])).

fof(f1692,plain,
    ( spl20_31
    | ~ spl20_2 ),
    inference(avatar_split_clause,[],[f946,f700,f1008])).

fof(f946,plain,
    ( r2_hidden(sK12(k3_xboole_0(k5_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),sK1)
    | ~ spl20_2 ),
    inference(resolution,[],[f701,f564])).
%------------------------------------------------------------------------------
