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
% DateTime   : Thu Dec  3 12:31:47 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 538 expanded)
%              Number of leaves         :   23 ( 200 expanded)
%              Depth                    :   11
%              Number of atoms          :  538 (3216 expanded)
%              Number of equality atoms :   47 ( 371 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1013,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f241,f266,f580,f607,f609,f610,f739,f792,f801,f804,f807,f808,f809,f831,f856,f857,f858,f859,f860,f867,f868,f869,f870,f872,f874,f875,f876,f877,f932,f1011,f1012])).

fof(f1012,plain,
    ( ~ spl7_19
    | spl7_15 ),
    inference(avatar_split_clause,[],[f557,f238,f732])).

fof(f732,plain,
    ( spl7_19
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f238,plain,
    ( spl7_15
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f557,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2))
    | spl7_15 ),
    inference(resolution,[],[f239,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f239,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f238])).

fof(f1011,plain,
    ( ~ spl7_16
    | spl7_3
    | spl7_19 ),
    inference(avatar_split_clause,[],[f1005,f732,f82,f270])).

fof(f270,plain,
    ( spl7_16
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f82,plain,
    ( spl7_3
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1005,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | spl7_19 ),
    inference(resolution,[],[f733,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f733,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f732])).

fof(f932,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f931])).

fof(f931,plain,
    ( $false
    | ~ spl7_13 ),
    inference(resolution,[],[f179,f54])).

fof(f54,plain,(
    ~ sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) ),
    inference(equality_proxy_replacement,[],[f42,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f42,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f24,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f24,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2))
   => k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f179,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_13
  <=> sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f877,plain,
    ( spl7_14
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f842,f824,f234])).

fof(f234,plain,
    ( spl7_14
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f824,plain,
    ( spl7_21
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f842,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | ~ spl7_21 ),
    inference(resolution,[],[f826,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f826,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f824])).

fof(f876,plain,
    ( ~ spl7_8
    | spl7_2 ),
    inference(avatar_split_clause,[],[f283,f78,f122])).

fof(f122,plain,
    ( spl7_8
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f78,plain,
    ( spl7_2
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f283,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0))
    | spl7_2 ),
    inference(resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f875,plain,
    ( ~ spl7_16
    | spl7_14
    | spl7_8 ),
    inference(avatar_split_clause,[],[f202,f122,f234,f270])).

fof(f202,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | spl7_8 ),
    inference(resolution,[],[f123,f50])).

fof(f123,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f874,plain,
    ( spl7_15
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f850,f828,f238])).

fof(f828,plain,
    ( spl7_22
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f850,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl7_22 ),
    inference(resolution,[],[f830,f52])).

fof(f830,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f828])).

fof(f872,plain,
    ( ~ spl7_14
    | spl7_16
    | spl7_7 ),
    inference(avatar_split_clause,[],[f288,f118,f270,f234])).

fof(f118,plain,
    ( spl7_7
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f288,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | spl7_7 ),
    inference(resolution,[],[f119,f50])).

fof(f119,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f870,plain,
    ( ~ spl7_3
    | spl7_16
    | spl7_15 ),
    inference(avatar_split_clause,[],[f571,f238,f270,f82])).

fof(f571,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | spl7_15 ),
    inference(resolution,[],[f558,f50])).

fof(f558,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1))
    | spl7_15 ),
    inference(resolution,[],[f239,f47])).

fof(f869,plain,
    ( ~ spl7_15
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f843,f824,f238])).

fof(f843,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl7_21 ),
    inference(resolution,[],[f826,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f868,plain,
    ( ~ spl7_2
    | spl7_3
    | spl7_13
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f816,f74,f177,f82,f78])).

fof(f74,plain,
    ( spl7_1
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f816,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f46,f53])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ( ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) ) )
          | r2_hidden(sK3(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK3(X0,X1,X2),X1)
              | ~ r2_hidden(sK3(X0,X1,X2),X2) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).

fof(f12,plain,(
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
     => ( ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) ) )
          | r2_hidden(sK3(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK3(X0,X1,X2),X1)
              | ~ r2_hidden(sK3(X0,X1,X2),X2) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r2_hidden(X3,X0)
        <~> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f75,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f867,plain,
    ( ~ spl7_3
    | spl7_2
    | spl7_13
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f817,f74,f177,f78,f82])).

fof(f817,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f45,f53])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f860,plain,
    ( ~ spl7_14
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f851,f828,f234])).

fof(f851,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f830,f51])).

fof(f859,plain,
    ( ~ spl7_14
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f602,f122,f234])).

fof(f602,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f124,f51])).

fof(f124,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f858,plain,
    ( spl7_16
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f754,f732,f270])).

fof(f754,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | ~ spl7_19 ),
    inference(resolution,[],[f734,f52])).

fof(f734,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f732])).

fof(f857,plain,
    ( ~ spl7_3
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f755,f732,f82])).

fof(f755,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ spl7_19 ),
    inference(resolution,[],[f734,f51])).

fof(f856,plain,
    ( ~ spl7_7
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f849])).

fof(f849,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_22 ),
    inference(resolution,[],[f830,f212])).

fof(f212,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(X0,sK0))
    | ~ spl7_7 ),
    inference(resolution,[],[f189,f51])).

fof(f189,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f120,f52])).

fof(f120,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f831,plain,
    ( spl7_21
    | spl7_22
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f818,f74,f828,f824])).

fof(f818,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))))
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f809,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f275,f82,f177,f78,f74])).

fof(f275,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f43,f53])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f808,plain,
    ( spl7_3
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f784,f736,f82])).

fof(f736,plain,
    ( spl7_20
  <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f784,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ spl7_20 ),
    inference(resolution,[],[f738,f52])).

fof(f738,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f736])).

fof(f807,plain,
    ( ~ spl7_16
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f785,f736,f270])).

fof(f785,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | ~ spl7_20 ),
    inference(resolution,[],[f738,f51])).

fof(f804,plain,
    ( spl7_1
    | ~ spl7_3
    | spl7_13
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f703,f118,f177,f82,f74])).

fof(f703,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ spl7_7 ),
    inference(resolution,[],[f193,f55])).

fof(f193,plain,
    ( ! [X2] : r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),X2))
    | ~ spl7_7 ),
    inference(resolution,[],[f120,f48])).

fof(f801,plain,
    ( ~ spl7_1
    | spl7_3
    | spl7_13
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f702,f118,f177,f82,f74])).

fof(f702,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | ~ spl7_7 ),
    inference(resolution,[],[f193,f58])).

fof(f792,plain,
    ( ~ spl7_16
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f190,f118,f270])).

fof(f190,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f120,f51])).

fof(f739,plain,
    ( spl7_19
    | spl7_20
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f726,f238,f736,f732])).

fof(f726,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2))
    | ~ spl7_15 ),
    inference(resolution,[],[f240,f49])).

fof(f240,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f238])).

fof(f610,plain,
    ( ~ spl7_15
    | spl7_14
    | spl7_1 ),
    inference(avatar_split_clause,[],[f246,f74,f234,f238])).

fof(f246,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl7_1 ),
    inference(resolution,[],[f129,f50])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))
    | spl7_1 ),
    inference(resolution,[],[f76,f47])).

fof(f76,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f609,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f112,f78,f122,f118])).

fof(f112,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1))
    | ~ spl7_2 ),
    inference(resolution,[],[f79,f49])).

fof(f79,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f607,plain,
    ( ~ spl7_8
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl7_8
    | spl7_16 ),
    inference(resolution,[],[f124,f293])).

fof(f293,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,X0))
    | spl7_16 ),
    inference(resolution,[],[f272,f52])).

fof(f272,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f270])).

fof(f580,plain,
    ( spl7_1
    | spl7_2
    | spl7_13
    | spl7_3 ),
    inference(avatar_split_clause,[],[f105,f82,f177,f78,f74])).

fof(f105,plain,
    ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))
    | spl7_3 ),
    inference(resolution,[],[f83,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f44,f53])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f266,plain,
    ( ~ spl7_7
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl7_7
    | spl7_14 ),
    inference(resolution,[],[f236,f189])).

fof(f236,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f234])).

fof(f241,plain,
    ( ~ spl7_14
    | spl7_15
    | spl7_1 ),
    inference(avatar_split_clause,[],[f228,f74,f238,f234])).

fof(f228,plain,
    ( r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)
    | spl7_1 ),
    inference(resolution,[],[f128,f50])).

fof(f128,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))))
    | spl7_1 ),
    inference(resolution,[],[f76,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:43:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.38  ipcrm: permission denied for id (812941314)
% 0.13/0.38  ipcrm: permission denied for id (813039622)
% 0.13/0.38  ipcrm: permission denied for id (813072391)
% 0.13/0.39  ipcrm: permission denied for id (813137930)
% 0.22/0.39  ipcrm: permission denied for id (813203469)
% 0.22/0.40  ipcrm: permission denied for id (813301777)
% 0.22/0.40  ipcrm: permission denied for id (813596699)
% 0.22/0.41  ipcrm: permission denied for id (813629468)
% 0.22/0.41  ipcrm: permission denied for id (813695006)
% 0.22/0.41  ipcrm: permission denied for id (813858852)
% 0.22/0.42  ipcrm: permission denied for id (813924391)
% 0.22/0.42  ipcrm: permission denied for id (814088238)
% 0.22/0.42  ipcrm: permission denied for id (814153777)
% 0.22/0.43  ipcrm: permission denied for id (814186547)
% 0.22/0.43  ipcrm: permission denied for id (814252084)
% 0.22/0.43  ipcrm: permission denied for id (814284853)
% 0.22/0.43  ipcrm: permission denied for id (814481468)
% 0.22/0.43  ipcrm: permission denied for id (814547006)
% 0.22/0.43  ipcrm: permission denied for id (814678080)
% 0.22/0.44  ipcrm: permission denied for id (814743619)
% 0.22/0.44  ipcrm: permission denied for id (814841927)
% 0.22/0.44  ipcrm: permission denied for id (814874697)
% 0.22/0.44  ipcrm: permission denied for id (814907466)
% 0.22/0.45  ipcrm: permission denied for id (815104079)
% 0.22/0.45  ipcrm: permission denied for id (815136848)
% 0.22/0.45  ipcrm: permission denied for id (815169618)
% 0.22/0.46  ipcrm: permission denied for id (815202387)
% 0.22/0.46  ipcrm: permission denied for id (815235156)
% 0.22/0.46  ipcrm: permission denied for id (815267925)
% 0.22/0.46  ipcrm: permission denied for id (815300694)
% 0.22/0.46  ipcrm: permission denied for id (815333463)
% 0.22/0.46  ipcrm: permission denied for id (815464539)
% 0.22/0.47  ipcrm: permission denied for id (815497311)
% 0.22/0.47  ipcrm: permission denied for id (815530080)
% 0.22/0.47  ipcrm: permission denied for id (815562849)
% 0.22/0.48  ipcrm: permission denied for id (815661156)
% 0.22/0.48  ipcrm: permission denied for id (815726694)
% 0.22/0.48  ipcrm: permission denied for id (815792232)
% 0.22/0.48  ipcrm: permission denied for id (815857770)
% 0.22/0.49  ipcrm: permission denied for id (815890539)
% 0.22/0.49  ipcrm: permission denied for id (816054386)
% 0.22/0.50  ipcrm: permission denied for id (816119924)
% 0.22/0.50  ipcrm: permission denied for id (816185463)
% 0.22/0.51  ipcrm: permission denied for id (816316539)
% 0.22/0.51  ipcrm: permission denied for id (816349309)
% 0.22/0.51  ipcrm: permission denied for id (816414847)
% 0.37/0.66  % (19183)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.37/0.66  % (19183)Refutation not found, incomplete strategy% (19183)------------------------------
% 0.37/0.66  % (19183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.66  % (19183)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.66  
% 0.37/0.66  % (19183)Memory used [KB]: 10618
% 0.37/0.66  % (19183)Time elapsed: 0.101 s
% 0.37/0.66  % (19183)------------------------------
% 0.37/0.66  % (19183)------------------------------
% 0.37/0.66  % (19179)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.37/0.67  % (19179)Refutation not found, incomplete strategy% (19179)------------------------------
% 0.37/0.67  % (19179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (19179)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.67  
% 0.37/0.67  % (19179)Memory used [KB]: 6140
% 0.37/0.67  % (19179)Time elapsed: 0.102 s
% 0.37/0.67  % (19179)------------------------------
% 0.37/0.67  % (19179)------------------------------
% 0.37/0.67  % (19191)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.37/0.67  % (19202)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.37/0.67  % (19180)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.37/0.67  % (19199)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.37/0.67  % (19181)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.37/0.68  % (19193)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.37/0.68  % (19177)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.37/0.68  % (19177)Refutation not found, incomplete strategy% (19177)------------------------------
% 0.37/0.68  % (19177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.68  % (19177)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.68  
% 0.37/0.68  % (19177)Memory used [KB]: 10618
% 0.37/0.68  % (19177)Time elapsed: 0.103 s
% 0.37/0.68  % (19177)------------------------------
% 0.37/0.68  % (19177)------------------------------
% 0.37/0.68  % (19188)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.37/0.68  % (19194)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.37/0.69  % (19174)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.51/0.69  % (19184)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.51/0.69  % (19201)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.51/0.69  % (19190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.51/0.69  % (19178)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.51/0.69  % (19187)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.51/0.70  % (19185)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.51/0.70  % (19205)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.51/0.70  % (19185)Refutation not found, incomplete strategy% (19185)------------------------------
% 0.51/0.70  % (19185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.70  % (19185)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.70  
% 0.51/0.70  % (19185)Memory used [KB]: 10618
% 0.51/0.70  % (19185)Time elapsed: 0.126 s
% 0.51/0.70  % (19185)------------------------------
% 0.51/0.70  % (19185)------------------------------
% 0.51/0.70  % (19182)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.51/0.70  % (19198)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.51/0.70  % (19176)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.51/0.70  % (19192)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.51/0.70  % (19186)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.51/0.70  % (19196)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.51/0.70  % (19192)Refutation not found, incomplete strategy% (19192)------------------------------
% 0.51/0.70  % (19192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.70  % (19192)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.70  
% 0.51/0.70  % (19192)Memory used [KB]: 10618
% 0.51/0.70  % (19192)Time elapsed: 0.141 s
% 0.51/0.70  % (19192)------------------------------
% 0.51/0.70  % (19192)------------------------------
% 0.51/0.70  % (19186)Refutation not found, incomplete strategy% (19186)------------------------------
% 0.51/0.70  % (19186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.70  % (19186)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.70  
% 0.51/0.70  % (19186)Memory used [KB]: 10618
% 0.51/0.70  % (19186)Time elapsed: 0.137 s
% 0.51/0.70  % (19186)------------------------------
% 0.51/0.70  % (19186)------------------------------
% 0.51/0.70  % (19201)Refutation not found, incomplete strategy% (19201)------------------------------
% 0.51/0.70  % (19201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.70  % (19203)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.51/0.70  % (19201)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.70  
% 0.51/0.70  % (19201)Memory used [KB]: 6268
% 0.51/0.70  % (19201)Time elapsed: 0.144 s
% 0.51/0.70  % (19201)------------------------------
% 0.51/0.70  % (19201)------------------------------
% 0.51/0.70  % (19189)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.51/0.70  % (19174)Refutation not found, incomplete strategy% (19174)------------------------------
% 0.51/0.70  % (19174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.70  % (19174)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.70  
% 0.51/0.70  % (19174)Memory used [KB]: 1791
% 0.51/0.70  % (19174)Time elapsed: 0.126 s
% 0.51/0.70  % (19174)------------------------------
% 0.51/0.70  % (19174)------------------------------
% 0.51/0.71  % (19195)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.51/0.71  % (19196)Refutation not found, incomplete strategy% (19196)------------------------------
% 0.51/0.71  % (19196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.71  % (19196)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.71  
% 0.51/0.71  % (19196)Memory used [KB]: 1663
% 0.51/0.71  % (19196)Time elapsed: 0.137 s
% 0.51/0.71  % (19196)------------------------------
% 0.51/0.71  % (19196)------------------------------
% 0.51/0.71  % (19200)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.51/0.72  % (19204)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.51/0.73  % (19195)Refutation not found, incomplete strategy% (19195)------------------------------
% 0.51/0.73  % (19195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.73  % (19195)Termination reason: Refutation not found, incomplete strategy
% 0.51/0.73  
% 0.51/0.73  % (19195)Memory used [KB]: 10618
% 0.51/0.73  % (19195)Time elapsed: 0.157 s
% 0.51/0.73  % (19195)------------------------------
% 0.51/0.73  % (19195)------------------------------
% 0.51/0.74  % (19190)Refutation found. Thanks to Tanya!
% 0.51/0.74  % SZS status Theorem for theBenchmark
% 0.86/0.77  % SZS output start Proof for theBenchmark
% 0.86/0.77  fof(f1013,plain,(
% 0.86/0.77    $false),
% 0.86/0.77    inference(avatar_sat_refutation,[],[f241,f266,f580,f607,f609,f610,f739,f792,f801,f804,f807,f808,f809,f831,f856,f857,f858,f859,f860,f867,f868,f869,f870,f872,f874,f875,f876,f877,f932,f1011,f1012])).
% 0.86/0.77  fof(f1012,plain,(
% 0.86/0.77    ~spl7_19 | spl7_15),
% 0.86/0.77    inference(avatar_split_clause,[],[f557,f238,f732])).
% 0.86/0.77  fof(f732,plain,(
% 0.86/0.77    spl7_19 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.86/0.77  fof(f238,plain,(
% 0.86/0.77    spl7_15 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.86/0.77  fof(f557,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2)) | spl7_15),
% 0.86/0.77    inference(resolution,[],[f239,f48])).
% 0.86/0.77  fof(f48,plain,(
% 0.86/0.77    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.86/0.77    inference(equality_resolution,[],[f31])).
% 0.86/0.77  fof(f31,plain,(
% 0.86/0.77    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.86/0.77    inference(cnf_transformation,[],[f18])).
% 0.86/0.77  fof(f18,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.86/0.77  fof(f17,plain,(
% 0.86/0.77    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.86/0.77    introduced(choice_axiom,[])).
% 0.86/0.77  fof(f16,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(rectify,[],[f15])).
% 0.86/0.77  fof(f15,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(flattening,[],[f14])).
% 0.86/0.77  fof(f14,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(nnf_transformation,[],[f1])).
% 0.86/0.77  fof(f1,axiom,(
% 0.86/0.77    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.86/0.77  fof(f239,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl7_15),
% 0.86/0.77    inference(avatar_component_clause,[],[f238])).
% 0.86/0.77  fof(f1011,plain,(
% 0.86/0.77    ~spl7_16 | spl7_3 | spl7_19),
% 0.86/0.77    inference(avatar_split_clause,[],[f1005,f732,f82,f270])).
% 0.86/0.77  fof(f270,plain,(
% 0.86/0.77    spl7_16 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1)),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.86/0.77  fof(f82,plain,(
% 0.86/0.77    spl7_3 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2)),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.86/0.77  fof(f1005,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | spl7_19),
% 0.86/0.77    inference(resolution,[],[f733,f50])).
% 0.86/0.77  fof(f50,plain,(
% 0.86/0.77    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.86/0.77    inference(equality_resolution,[],[f38])).
% 0.86/0.77  fof(f38,plain,(
% 0.86/0.77    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.86/0.77    inference(cnf_transformation,[],[f23])).
% 0.86/0.77  fof(f23,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 0.86/0.77  fof(f22,plain,(
% 0.86/0.77    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.86/0.77    introduced(choice_axiom,[])).
% 0.86/0.77  fof(f21,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(rectify,[],[f20])).
% 0.86/0.77  fof(f20,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(flattening,[],[f19])).
% 0.86/0.77  fof(f19,plain,(
% 0.86/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.86/0.77    inference(nnf_transformation,[],[f2])).
% 0.86/0.77  fof(f2,axiom,(
% 0.86/0.77    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.86/0.77  fof(f733,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2)) | spl7_19),
% 0.86/0.77    inference(avatar_component_clause,[],[f732])).
% 0.86/0.77  fof(f932,plain,(
% 0.86/0.77    ~spl7_13),
% 0.86/0.77    inference(avatar_contradiction_clause,[],[f931])).
% 0.86/0.77  fof(f931,plain,(
% 0.86/0.77    $false | ~spl7_13),
% 0.86/0.77    inference(resolution,[],[f179,f54])).
% 0.86/0.77  fof(f54,plain,(
% 0.86/0.77    ~sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))),
% 0.86/0.77    inference(equality_proxy_replacement,[],[f42,f53])).
% 0.86/0.77  fof(f53,plain,(
% 0.86/0.77    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.86/0.77    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.86/0.77  fof(f42,plain,(
% 0.86/0.77    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))),
% 0.86/0.77    inference(definition_unfolding,[],[f24,f25,f25,f25,f25])).
% 0.86/0.77  fof(f25,plain,(
% 0.86/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.86/0.77    inference(cnf_transformation,[],[f3])).
% 0.86/0.77  fof(f3,axiom,(
% 0.86/0.77    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.86/0.77  fof(f24,plain,(
% 0.86/0.77    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 0.86/0.77    inference(cnf_transformation,[],[f10])).
% 0.86/0.77  fof(f10,plain,(
% 0.86/0.77    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 0.86/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.86/0.77  fof(f9,plain,(
% 0.86/0.77    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2)) => k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 0.86/0.77    introduced(choice_axiom,[])).
% 0.86/0.77  fof(f7,plain,(
% 0.86/0.77    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.86/0.77    inference(ennf_transformation,[],[f6])).
% 0.86/0.77  fof(f6,negated_conjecture,(
% 0.86/0.77    ~! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.86/0.77    inference(negated_conjecture,[],[f5])).
% 0.86/0.77  fof(f5,conjecture,(
% 0.86/0.77    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.86/0.77  fof(f179,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~spl7_13),
% 0.86/0.77    inference(avatar_component_clause,[],[f177])).
% 0.86/0.77  fof(f177,plain,(
% 0.86/0.77    spl7_13 <=> sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.86/0.77  fof(f877,plain,(
% 0.86/0.77    spl7_14 | ~spl7_21),
% 0.86/0.77    inference(avatar_split_clause,[],[f842,f824,f234])).
% 0.86/0.77  fof(f234,plain,(
% 0.86/0.77    spl7_14 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0)),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.86/0.77  fof(f824,plain,(
% 0.86/0.77    spl7_21 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.86/0.77  fof(f842,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | ~spl7_21),
% 0.86/0.77    inference(resolution,[],[f826,f52])).
% 0.86/0.77  fof(f52,plain,(
% 0.86/0.77    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.86/0.77    inference(equality_resolution,[],[f36])).
% 0.86/0.77  fof(f36,plain,(
% 0.86/0.77    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.86/0.77    inference(cnf_transformation,[],[f23])).
% 0.86/0.77  fof(f826,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))) | ~spl7_21),
% 0.86/0.77    inference(avatar_component_clause,[],[f824])).
% 0.86/0.77  fof(f876,plain,(
% 0.86/0.77    ~spl7_8 | spl7_2),
% 0.86/0.77    inference(avatar_split_clause,[],[f283,f78,f122])).
% 0.86/0.77  fof(f122,plain,(
% 0.86/0.77    spl7_8 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.86/0.77  fof(f78,plain,(
% 0.86/0.77    spl7_2 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.86/0.77  fof(f283,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0)) | spl7_2),
% 0.86/0.77    inference(resolution,[],[f80,f47])).
% 0.86/0.77  fof(f47,plain,(
% 0.86/0.77    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.86/0.77    inference(equality_resolution,[],[f32])).
% 0.86/0.77  fof(f32,plain,(
% 0.86/0.77    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.86/0.77    inference(cnf_transformation,[],[f18])).
% 0.86/0.77  fof(f80,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl7_2),
% 0.86/0.77    inference(avatar_component_clause,[],[f78])).
% 0.86/0.77  fof(f875,plain,(
% 0.86/0.77    ~spl7_16 | spl7_14 | spl7_8),
% 0.86/0.77    inference(avatar_split_clause,[],[f202,f122,f234,f270])).
% 0.86/0.77  fof(f202,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | spl7_8),
% 0.86/0.77    inference(resolution,[],[f123,f50])).
% 0.86/0.77  fof(f123,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0)) | spl7_8),
% 0.86/0.77    inference(avatar_component_clause,[],[f122])).
% 0.86/0.77  fof(f874,plain,(
% 0.86/0.77    spl7_15 | ~spl7_22),
% 0.86/0.77    inference(avatar_split_clause,[],[f850,f828,f238])).
% 0.86/0.77  fof(f828,plain,(
% 0.86/0.77    spl7_22 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.86/0.77  fof(f850,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~spl7_22),
% 0.86/0.77    inference(resolution,[],[f830,f52])).
% 0.86/0.77  fof(f830,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)) | ~spl7_22),
% 0.86/0.77    inference(avatar_component_clause,[],[f828])).
% 0.86/0.77  fof(f872,plain,(
% 0.86/0.77    ~spl7_14 | spl7_16 | spl7_7),
% 0.86/0.77    inference(avatar_split_clause,[],[f288,f118,f270,f234])).
% 0.86/0.77  fof(f118,plain,(
% 0.86/0.77    spl7_7 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.86/0.77  fof(f288,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | spl7_7),
% 0.86/0.77    inference(resolution,[],[f119,f50])).
% 0.86/0.77  fof(f119,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1)) | spl7_7),
% 0.86/0.77    inference(avatar_component_clause,[],[f118])).
% 0.86/0.77  fof(f870,plain,(
% 0.86/0.77    ~spl7_3 | spl7_16 | spl7_15),
% 0.86/0.77    inference(avatar_split_clause,[],[f571,f238,f270,f82])).
% 0.86/0.77  fof(f571,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | spl7_15),
% 0.86/0.77    inference(resolution,[],[f558,f50])).
% 0.86/0.77  fof(f558,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1)) | spl7_15),
% 0.86/0.77    inference(resolution,[],[f239,f47])).
% 0.86/0.77  fof(f869,plain,(
% 0.86/0.77    ~spl7_15 | ~spl7_21),
% 0.86/0.77    inference(avatar_split_clause,[],[f843,f824,f238])).
% 0.86/0.77  fof(f843,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~spl7_21),
% 0.86/0.77    inference(resolution,[],[f826,f51])).
% 0.86/0.77  fof(f51,plain,(
% 0.86/0.77    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.86/0.77    inference(equality_resolution,[],[f37])).
% 0.86/0.77  fof(f37,plain,(
% 0.86/0.77    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.86/0.77    inference(cnf_transformation,[],[f23])).
% 0.86/0.77  fof(f868,plain,(
% 0.86/0.77    ~spl7_2 | spl7_3 | spl7_13 | ~spl7_1),
% 0.86/0.77    inference(avatar_split_clause,[],[f816,f74,f177,f82,f78])).
% 0.86/0.77  fof(f74,plain,(
% 0.86/0.77    spl7_1 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.86/0.77  fof(f816,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~spl7_1),
% 0.86/0.77    inference(resolution,[],[f75,f58])).
% 0.86/0.77  fof(f58,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(equality_proxy_replacement,[],[f46,f53])).
% 0.86/0.77  fof(f46,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0 | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(definition_unfolding,[],[f26,f25])).
% 0.86/0.77  fof(f26,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k5_xboole_0(X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(cnf_transformation,[],[f13])).
% 0.86/0.77  fof(f13,plain,(
% 0.86/0.77    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ((((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1))) | r2_hidden(sK3(X0,X1,X2),X0)) & (((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1))) | ~r2_hidden(sK3(X0,X1,X2),X0))))),
% 0.86/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).
% 0.86/0.77  fof(f12,plain,(
% 0.86/0.77    ! [X2,X1,X0] : (? [X3] : ((((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | r2_hidden(X3,X0)) & (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~r2_hidden(X3,X0))) => ((((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1))) | r2_hidden(sK3(X0,X1,X2),X0)) & (((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1))) | ~r2_hidden(sK3(X0,X1,X2),X0))))),
% 0.86/0.77    introduced(choice_axiom,[])).
% 0.86/0.77  fof(f11,plain,(
% 0.86/0.77    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ? [X3] : ((((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | r2_hidden(X3,X0)) & (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~r2_hidden(X3,X0))))),
% 0.86/0.77    inference(nnf_transformation,[],[f8])).
% 0.86/0.77  fof(f8,plain,(
% 0.86/0.77    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ? [X3] : (~r2_hidden(X3,X0) <~> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))))),
% 0.86/0.77    inference(ennf_transformation,[],[f4])).
% 0.86/0.77  fof(f4,axiom,(
% 0.86/0.77    ! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 0.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).
% 0.86/0.77  fof(f75,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~spl7_1),
% 0.86/0.77    inference(avatar_component_clause,[],[f74])).
% 0.86/0.77  fof(f867,plain,(
% 0.86/0.77    ~spl7_3 | spl7_2 | spl7_13 | ~spl7_1),
% 0.86/0.77    inference(avatar_split_clause,[],[f817,f74,f177,f78,f82])).
% 0.86/0.77  fof(f817,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~spl7_1),
% 0.86/0.77    inference(resolution,[],[f75,f57])).
% 0.86/0.77  fof(f57,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(equality_proxy_replacement,[],[f45,f53])).
% 0.86/0.77  fof(f45,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(definition_unfolding,[],[f27,f25])).
% 0.86/0.77  fof(f27,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k5_xboole_0(X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(cnf_transformation,[],[f13])).
% 0.86/0.77  fof(f860,plain,(
% 0.86/0.77    ~spl7_14 | ~spl7_22),
% 0.86/0.77    inference(avatar_split_clause,[],[f851,f828,f234])).
% 0.86/0.77  fof(f851,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | ~spl7_22),
% 0.86/0.77    inference(resolution,[],[f830,f51])).
% 0.86/0.77  fof(f859,plain,(
% 0.86/0.77    ~spl7_14 | ~spl7_8),
% 0.86/0.77    inference(avatar_split_clause,[],[f602,f122,f234])).
% 0.86/0.77  fof(f602,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | ~spl7_8),
% 0.86/0.77    inference(resolution,[],[f124,f51])).
% 0.86/0.77  fof(f124,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0)) | ~spl7_8),
% 0.86/0.77    inference(avatar_component_clause,[],[f122])).
% 0.86/0.77  fof(f858,plain,(
% 0.86/0.77    spl7_16 | ~spl7_19),
% 0.86/0.77    inference(avatar_split_clause,[],[f754,f732,f270])).
% 0.86/0.77  fof(f754,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | ~spl7_19),
% 0.86/0.77    inference(resolution,[],[f734,f52])).
% 0.86/0.77  fof(f734,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2)) | ~spl7_19),
% 0.86/0.77    inference(avatar_component_clause,[],[f732])).
% 0.86/0.77  fof(f857,plain,(
% 0.86/0.77    ~spl7_3 | ~spl7_19),
% 0.86/0.77    inference(avatar_split_clause,[],[f755,f732,f82])).
% 0.86/0.77  fof(f755,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~spl7_19),
% 0.86/0.77    inference(resolution,[],[f734,f51])).
% 0.86/0.77  fof(f856,plain,(
% 0.86/0.77    ~spl7_7 | ~spl7_22),
% 0.86/0.77    inference(avatar_contradiction_clause,[],[f849])).
% 0.86/0.77  fof(f849,plain,(
% 0.86/0.77    $false | (~spl7_7 | ~spl7_22)),
% 0.86/0.77    inference(resolution,[],[f830,f212])).
% 0.86/0.77  fof(f212,plain,(
% 0.86/0.77    ( ! [X0] : (~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(X0,sK0))) ) | ~spl7_7),
% 0.86/0.77    inference(resolution,[],[f189,f51])).
% 0.86/0.77  fof(f189,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | ~spl7_7),
% 0.86/0.77    inference(resolution,[],[f120,f52])).
% 0.86/0.77  fof(f120,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1)) | ~spl7_7),
% 0.86/0.77    inference(avatar_component_clause,[],[f118])).
% 0.86/0.77  fof(f831,plain,(
% 0.86/0.77    spl7_21 | spl7_22 | ~spl7_1),
% 0.86/0.77    inference(avatar_split_clause,[],[f818,f74,f828,f824])).
% 0.86/0.77  fof(f818,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))) | ~spl7_1),
% 0.86/0.77    inference(resolution,[],[f75,f49])).
% 0.86/0.77  fof(f49,plain,(
% 0.86/0.77    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.86/0.77    inference(equality_resolution,[],[f30])).
% 0.86/0.77  fof(f30,plain,(
% 0.86/0.77    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.86/0.77    inference(cnf_transformation,[],[f18])).
% 0.86/0.77  fof(f809,plain,(
% 0.86/0.77    spl7_1 | ~spl7_2 | spl7_13 | ~spl7_3),
% 0.86/0.77    inference(avatar_split_clause,[],[f275,f82,f177,f78,f74])).
% 0.86/0.77  fof(f275,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~spl7_3),
% 0.86/0.77    inference(resolution,[],[f84,f55])).
% 0.86/0.77  fof(f55,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(equality_proxy_replacement,[],[f43,f53])).
% 0.86/0.77  fof(f43,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(definition_unfolding,[],[f29,f25])).
% 0.86/0.77  fof(f29,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k5_xboole_0(X1,X2) = X0 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(cnf_transformation,[],[f13])).
% 0.86/0.77  fof(f84,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~spl7_3),
% 0.86/0.77    inference(avatar_component_clause,[],[f82])).
% 0.86/0.77  fof(f808,plain,(
% 0.86/0.77    spl7_3 | ~spl7_20),
% 0.86/0.77    inference(avatar_split_clause,[],[f784,f736,f82])).
% 0.86/0.77  fof(f736,plain,(
% 0.86/0.77    spl7_20 <=> r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1))),
% 0.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.86/0.77  fof(f784,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~spl7_20),
% 0.86/0.77    inference(resolution,[],[f738,f52])).
% 0.86/0.77  fof(f738,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1)) | ~spl7_20),
% 0.86/0.77    inference(avatar_component_clause,[],[f736])).
% 0.86/0.77  fof(f807,plain,(
% 0.86/0.77    ~spl7_16 | ~spl7_20),
% 0.86/0.77    inference(avatar_split_clause,[],[f785,f736,f270])).
% 0.86/0.77  fof(f785,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | ~spl7_20),
% 0.86/0.77    inference(resolution,[],[f738,f51])).
% 0.86/0.77  fof(f804,plain,(
% 0.86/0.77    spl7_1 | ~spl7_3 | spl7_13 | ~spl7_7),
% 0.86/0.77    inference(avatar_split_clause,[],[f703,f118,f177,f82,f74])).
% 0.86/0.77  fof(f703,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~spl7_7),
% 0.86/0.77    inference(resolution,[],[f193,f55])).
% 0.86/0.77  fof(f193,plain,(
% 0.86/0.77    ( ! [X2] : (r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),X2))) ) | ~spl7_7),
% 0.86/0.77    inference(resolution,[],[f120,f48])).
% 0.86/0.77  fof(f801,plain,(
% 0.86/0.77    ~spl7_1 | spl7_3 | spl7_13 | ~spl7_7),
% 0.86/0.77    inference(avatar_split_clause,[],[f702,f118,f177,f82,f74])).
% 0.86/0.77  fof(f702,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | ~spl7_7),
% 0.86/0.77    inference(resolution,[],[f193,f58])).
% 0.86/0.77  fof(f792,plain,(
% 0.86/0.77    ~spl7_16 | ~spl7_7),
% 0.86/0.77    inference(avatar_split_clause,[],[f190,f118,f270])).
% 0.86/0.77  fof(f190,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | ~spl7_7),
% 0.86/0.77    inference(resolution,[],[f120,f51])).
% 0.86/0.77  fof(f739,plain,(
% 0.86/0.77    spl7_19 | spl7_20 | ~spl7_15),
% 0.86/0.77    inference(avatar_split_clause,[],[f726,f238,f736,f732])).
% 0.86/0.77  fof(f726,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,sK1)) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK2)) | ~spl7_15),
% 0.86/0.77    inference(resolution,[],[f240,f49])).
% 0.86/0.77  fof(f240,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~spl7_15),
% 0.86/0.77    inference(avatar_component_clause,[],[f238])).
% 0.86/0.77  fof(f610,plain,(
% 0.86/0.77    ~spl7_15 | spl7_14 | spl7_1),
% 0.86/0.77    inference(avatar_split_clause,[],[f246,f74,f234,f238])).
% 0.86/0.77  fof(f246,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl7_1),
% 0.86/0.77    inference(resolution,[],[f129,f50])).
% 0.86/0.77  fof(f129,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)) | spl7_1),
% 0.86/0.77    inference(resolution,[],[f76,f47])).
% 0.86/0.77  fof(f76,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | spl7_1),
% 0.86/0.77    inference(avatar_component_clause,[],[f74])).
% 0.86/0.77  fof(f609,plain,(
% 0.86/0.77    spl7_7 | spl7_8 | ~spl7_2),
% 0.86/0.77    inference(avatar_split_clause,[],[f112,f78,f122,f118])).
% 0.86/0.77  fof(f112,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,sK0)) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,sK1)) | ~spl7_2),
% 0.86/0.77    inference(resolution,[],[f79,f49])).
% 0.86/0.77  fof(f79,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~spl7_2),
% 0.86/0.77    inference(avatar_component_clause,[],[f78])).
% 0.86/0.77  fof(f607,plain,(
% 0.86/0.77    ~spl7_8 | spl7_16),
% 0.86/0.77    inference(avatar_contradiction_clause,[],[f600])).
% 0.86/0.77  fof(f600,plain,(
% 0.86/0.77    $false | (~spl7_8 | spl7_16)),
% 0.86/0.77    inference(resolution,[],[f124,f293])).
% 0.86/0.77  fof(f293,plain,(
% 0.86/0.77    ( ! [X0] : (~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK1,X0))) ) | spl7_16),
% 0.86/0.77    inference(resolution,[],[f272,f52])).
% 0.86/0.77  fof(f272,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK1) | spl7_16),
% 0.86/0.77    inference(avatar_component_clause,[],[f270])).
% 0.86/0.77  fof(f580,plain,(
% 0.86/0.77    spl7_1 | spl7_2 | spl7_13 | spl7_3),
% 0.86/0.77    inference(avatar_split_clause,[],[f105,f82,f177,f78,f74])).
% 0.86/0.77  fof(f105,plain,(
% 0.86/0.77    sQ6_eqProxy(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0))) | spl7_3),
% 0.86/0.77    inference(resolution,[],[f83,f56])).
% 0.86/0.77  fof(f56,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0) | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(equality_proxy_replacement,[],[f44,f53])).
% 0.86/0.77  fof(f44,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(definition_unfolding,[],[f28,f25])).
% 0.86/0.77  fof(f28,plain,(
% 0.86/0.77    ( ! [X2,X0,X1] : (k5_xboole_0(X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.86/0.77    inference(cnf_transformation,[],[f13])).
% 0.86/0.77  fof(f83,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK2) | spl7_3),
% 0.86/0.77    inference(avatar_component_clause,[],[f82])).
% 0.86/0.77  fof(f266,plain,(
% 0.86/0.77    ~spl7_7 | spl7_14),
% 0.86/0.77    inference(avatar_contradiction_clause,[],[f261])).
% 0.86/0.77  fof(f261,plain,(
% 0.86/0.77    $false | (~spl7_7 | spl7_14)),
% 0.86/0.77    inference(resolution,[],[f236,f189])).
% 0.86/0.77  fof(f236,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | spl7_14),
% 0.86/0.77    inference(avatar_component_clause,[],[f234])).
% 0.86/0.77  fof(f241,plain,(
% 0.86/0.77    ~spl7_14 | spl7_15 | spl7_1),
% 0.86/0.77    inference(avatar_split_clause,[],[f228,f74,f238,f234])).
% 0.86/0.77  fof(f228,plain,(
% 0.86/0.77    r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),sK0) | spl7_1),
% 0.86/0.77    inference(resolution,[],[f128,f50])).
% 0.86/0.77  fof(f128,plain,(
% 0.86/0.77    ~r2_hidden(sK3(k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))) | spl7_1),
% 0.86/0.77    inference(resolution,[],[f76,f48])).
% 0.86/0.77  % SZS output end Proof for theBenchmark
% 0.86/0.77  % (19190)------------------------------
% 0.86/0.77  % (19190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.86/0.77  % (19190)Termination reason: Refutation
% 0.86/0.77  
% 0.86/0.77  % (19190)Memory used [KB]: 6652
% 0.86/0.77  % (19190)Time elapsed: 0.183 s
% 0.86/0.77  % (19190)------------------------------
% 0.86/0.77  % (19190)------------------------------
% 0.86/0.77  % (19006)Success in time 0.398 s
%------------------------------------------------------------------------------
