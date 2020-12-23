%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 265 expanded)
%              Number of leaves         :   12 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  330 (1495 expanded)
%              Number of equality atoms :   39 ( 210 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2209,f2217,f2237,f2255,f2258,f2282])).

fof(f2282,plain,
    ( spl19_127
    | ~ spl19_17 ),
    inference(avatar_split_clause,[],[f2261,f737,f2212])).

fof(f2212,plain,
    ( spl19_127
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_127])])).

fof(f737,plain,
    ( spl19_17
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_17])])).

fof(f2261,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1)
    | ~ spl19_17 ),
    inference(resolution,[],[f738,f510])).

fof(f510,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f471])).

fof(f471,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f298])).

fof(f298,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f296,f297])).

fof(f297,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f296,plain,(
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
    inference(rectify,[],[f295])).

fof(f295,plain,(
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
    inference(flattening,[],[f294])).

fof(f294,plain,(
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

fof(f738,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | ~ spl19_17 ),
    inference(avatar_component_clause,[],[f737])).

fof(f2258,plain,
    ( spl19_17
    | spl19_16 ),
    inference(avatar_split_clause,[],[f2257,f733,f737])).

fof(f733,plain,
    ( spl19_16
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_16])])).

fof(f2257,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | spl19_16 ),
    inference(subsumption_resolution,[],[f2256,f730])).

fof(f730,plain,(
    ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f729,f512])).

fof(f512,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f478])).

fof(f478,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f303])).

fof(f303,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
              & ~ r2_hidden(sK14(X0,X1,X2),X0) )
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( r2_hidden(sK14(X0,X1,X2),X1)
            | r2_hidden(sK14(X0,X1,X2),X0)
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f301,f302])).

fof(f302,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            & ~ r2_hidden(sK14(X0,X1,X2),X0) )
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( r2_hidden(sK14(X0,X1,X2),X1)
          | r2_hidden(sK14(X0,X1,X2),X0)
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f301,plain,(
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
    inference(rectify,[],[f300])).

fof(f300,plain,(
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
    inference(flattening,[],[f299])).

fof(f299,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f729,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f715,f509])).

fof(f509,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f472])).

fof(f472,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f298])).

fof(f715,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f628,f600])).

fof(f600,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f461,f516])).

fof(f516,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f461,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f288])).

fof(f288,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ( ( ( ( ~ r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | r2_hidden(sK11(X0,X1,X2),X1) ) )
          | r2_hidden(sK11(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK11(X0,X1,X2),X1)
              | ~ r2_hidden(sK11(X0,X1,X2),X2) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f286,f287])).

fof(f287,plain,(
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
     => ( ( ( ( ~ r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | r2_hidden(sK11(X0,X1,X2),X1) ) )
          | r2_hidden(sK11(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK11(X0,X1,X2),X1)
              | ~ r2_hidden(sK11(X0,X1,X2),X2) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f286,plain,(
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
    inference(nnf_transformation,[],[f237])).

fof(f237,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f628,plain,(
    ~ sQ18_eqProxy(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f521,f612])).

fof(f612,plain,(
    ! [X0,X1] :
      ( ~ sQ18_eqProxy(X0,X1)
      | sQ18_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f516])).

fof(f521,plain,(
    ~ sQ18_eqProxy(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(equality_proxy_replacement,[],[f309,f516])).

fof(f309,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f157,f253])).

fof(f253,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f157,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f150])).

fof(f150,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f149])).

fof(f149,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f2256,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | spl19_16 ),
    inference(subsumption_resolution,[],[f2240,f628])).

fof(f2240,plain,
    ( sQ18_eqProxy(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | spl19_16 ),
    inference(resolution,[],[f735,f598])).

fof(f598,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X2)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f463,f516])).

fof(f463,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK11(X0,X1,X2),X2)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f288])).

fof(f735,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))
    | spl19_16 ),
    inference(avatar_component_clause,[],[f733])).

fof(f2255,plain,
    ( ~ spl19_127
    | spl19_16 ),
    inference(avatar_split_clause,[],[f2239,f733,f2212])).

fof(f2239,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1)
    | spl19_16 ),
    inference(resolution,[],[f735,f511])).

fof(f511,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f479])).

fof(f479,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f303])).

fof(f2237,plain,
    ( ~ spl19_127
    | spl19_17 ),
    inference(avatar_split_clause,[],[f2236,f737,f2212])).

fof(f2236,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1)
    | spl19_17 ),
    inference(subsumption_resolution,[],[f2220,f730])).

fof(f2220,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1)
    | spl19_17 ),
    inference(resolution,[],[f739,f508])).

fof(f508,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f473])).

fof(f473,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f298])).

fof(f739,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | spl19_17 ),
    inference(avatar_component_clause,[],[f737])).

fof(f2217,plain,
    ( spl19_127
    | ~ spl19_16 ),
    inference(avatar_split_clause,[],[f2216,f733,f2212])).

fof(f2216,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1)
    | ~ spl19_16 ),
    inference(subsumption_resolution,[],[f2187,f730])).

fof(f2187,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK1)
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | ~ spl19_16 ),
    inference(resolution,[],[f734,f513])).

fof(f513,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f477])).

fof(f477,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f303])).

fof(f734,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))
    | ~ spl19_16 ),
    inference(avatar_component_clause,[],[f733])).

fof(f2209,plain,
    ( ~ spl19_17
    | ~ spl19_16 ),
    inference(avatar_split_clause,[],[f2208,f733,f737])).

fof(f2208,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | ~ spl19_16 ),
    inference(subsumption_resolution,[],[f2207,f730])).

fof(f2207,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | ~ spl19_16 ),
    inference(subsumption_resolution,[],[f2184,f628])).

fof(f2184,plain,
    ( sQ18_eqProxy(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0))
    | ~ spl19_16 ),
    inference(resolution,[],[f734,f599])).

fof(f599,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f462,f516])).

fof(f462,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f288])).
%------------------------------------------------------------------------------
