%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0048+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 236 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  292 (1585 expanded)
%              Number of equality atoms :   35 ( 216 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f570,f771,f827,f1293])).

fof(f1293,plain,
    ( spl19_3
    | ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f1292])).

fof(f1292,plain,
    ( $false
    | spl19_3
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1291,f564])).

fof(f564,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl19_3 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl19_3
  <=> r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f1291,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1286,f338])).

fof(f338,plain,(
    ~ sQ18_eqProxy(k4_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f200,f335])).

fof(f335,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f200,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f96,f147])).

fof(f147,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
   => k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f78])).

fof(f78,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1286,plain,
    ( sQ18_eqProxy(k4_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl19_4 ),
    inference(resolution,[],[f847,f391])).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK13(X0,X1,X2),X1)
      | sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f297,f335])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f182,f183])).

fof(f183,plain,(
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

fof(f182,plain,(
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
    inference(rectify,[],[f181])).

fof(f181,plain,(
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
    inference(flattening,[],[f180])).

fof(f180,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f847,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f843,f776])).

fof(f776,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl19_4 ),
    inference(resolution,[],[f569,f327])).

fof(f327,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f294])).

fof(f294,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f569,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f567])).

fof(f567,plain,
    ( spl19_4
  <=> r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f843,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl19_4 ),
    inference(resolution,[],[f842,f334])).

fof(f334,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f305])).

fof(f305,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
              & ~ r2_hidden(sK15(X0,X1,X2),X0) )
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( r2_hidden(sK15(X0,X1,X2),X1)
            | r2_hidden(sK15(X0,X1,X2),X0)
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f192,f193])).

fof(f193,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            & ~ r2_hidden(sK15(X0,X1,X2),X0) )
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( r2_hidden(sK15(X0,X1,X2),X1)
          | r2_hidden(sK15(X0,X1,X2),X0)
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f192,plain,(
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
    inference(rectify,[],[f191])).

fof(f191,plain,(
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
    inference(flattening,[],[f190])).

fof(f190,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f842,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f830,f775])).

fof(f775,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_4 ),
    inference(resolution,[],[f569,f328])).

fof(f328,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f293])).

fof(f293,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f830,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f829,f332])).

fof(f332,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f307])).

fof(f307,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f829,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f639,f569])).

fof(f639,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    inference(resolution,[],[f479,f338])).

fof(f479,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3))
      | ~ r2_hidden(sK13(X0,X1,k4_xboole_0(X2,X3)),X0)
      | r2_hidden(sK13(X0,X1,k4_xboole_0(X2,X3)),X1)
      | r2_hidden(sK13(X0,X1,k4_xboole_0(X2,X3)),X3)
      | ~ r2_hidden(sK13(X0,X1,k4_xboole_0(X2,X3)),X2) ) ),
    inference(resolution,[],[f390,f326])).

fof(f326,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f295])).

fof(f295,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK13(X0,X1,X2),X2)
      | r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | sQ18_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f298,f335])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f827,plain,
    ( ~ spl19_3
    | ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | ~ spl19_3
    | ~ spl19_4 ),
    inference(unit_resulting_resolution,[],[f584,f821,f332])).

fof(f821,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl19_3
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f773,f569])).

fof(f773,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f772,f583])).

fof(f583,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_3 ),
    inference(resolution,[],[f565,f328])).

fof(f565,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f563])).

fof(f772,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f639,f584])).

fof(f584,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl19_3 ),
    inference(resolution,[],[f565,f327])).

fof(f771,plain,
    ( ~ spl19_3
    | spl19_4 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | ~ spl19_3
    | spl19_4 ),
    inference(unit_resulting_resolution,[],[f584,f758,f333])).

fof(f333,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f306])).

fof(f306,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f758,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl19_3
    | spl19_4 ),
    inference(subsumption_resolution,[],[f576,f583])).

fof(f576,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl19_4 ),
    inference(resolution,[],[f568,f326])).

fof(f568,plain,
    ( ~ r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | spl19_4 ),
    inference(avatar_component_clause,[],[f567])).

fof(f570,plain,
    ( spl19_3
    | spl19_4 ),
    inference(avatar_split_clause,[],[f475,f567,f563])).

fof(f475,plain,
    ( r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK13(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f392,f338])).

fof(f392,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f296,f335])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f184])).
%------------------------------------------------------------------------------
