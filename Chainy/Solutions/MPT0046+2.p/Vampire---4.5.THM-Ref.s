%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0046+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 174 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  247 (1061 expanded)
%              Number of equality atoms :   34 ( 165 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f906,f928,f1635,f1670])).

fof(f1670,plain,
    ( spl18_11
    | ~ spl18_12 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | spl18_11
    | ~ spl18_12 ),
    inference(unit_resulting_resolution,[],[f904,f672,f1654,f322])).

fof(f322,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f291])).

fof(f291,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f182])).

fof(f182,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f180,f181])).

fof(f181,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f179])).

fof(f179,plain,(
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
    inference(flattening,[],[f178])).

fof(f178,plain,(
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

fof(f1654,plain,
    ( ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | spl18_11 ),
    inference(resolution,[],[f901,f328])).

fof(f328,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f303])).

fof(f303,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f190,f191])).

fof(f191,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f189])).

fof(f189,plain,(
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
    inference(flattening,[],[f188])).

fof(f188,plain,(
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

fof(f901,plain,
    ( ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | spl18_11 ),
    inference(avatar_component_clause,[],[f899])).

fof(f899,plain,
    ( spl18_11
  <=> r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f672,plain,(
    ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f669,f329])).

fof(f329,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f302])).

fof(f302,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f192])).

fof(f669,plain,
    ( ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK0)
    | ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f391,f334])).

fof(f334,plain,(
    ~ sQ17_eqProxy(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(equality_proxy_replacement,[],[f198,f331])).

fof(f331,plain,(
    ! [X1,X0] :
      ( sQ17_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).

fof(f198,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f94,f145])).

fof(f145,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f74])).

fof(f74,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f305,f331])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f904,plain,
    ( r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl18_12 ),
    inference(avatar_component_clause,[],[f903])).

fof(f903,plain,
    ( spl18_12
  <=> r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f1635,plain,
    ( ~ spl18_11
    | spl18_12 ),
    inference(avatar_contradiction_clause,[],[f1634])).

fof(f1634,plain,
    ( $false
    | ~ spl18_11
    | spl18_12 ),
    inference(subsumption_resolution,[],[f1626,f905])).

fof(f905,plain,
    ( ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK1)
    | spl18_12 ),
    inference(avatar_component_clause,[],[f903])).

fof(f1626,plain,
    ( r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl18_11 ),
    inference(resolution,[],[f934,f324])).

fof(f324,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f289])).

fof(f289,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f182])).

fof(f934,plain,
    ( r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f929,f672])).

fof(f929,plain,
    ( r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK0)
    | r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | ~ spl18_11 ),
    inference(resolution,[],[f900,f330])).

fof(f330,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f301])).

fof(f301,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f192])).

fof(f900,plain,
    ( r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ spl18_11 ),
    inference(avatar_component_clause,[],[f899])).

fof(f928,plain,
    ( spl18_11
    | spl18_12 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | spl18_11
    | spl18_12 ),
    inference(unit_resulting_resolution,[],[f334,f672,f905,f901,f392])).

fof(f392,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f304,f331])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f906,plain,
    ( ~ spl18_11
    | ~ spl18_12 ),
    inference(avatar_split_clause,[],[f662,f903,f899])).

fof(f662,plain,
    ( ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK1)
    | ~ r2_hidden(sK14(sK0,sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f390,f334])).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f306,f331])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f192])).
%------------------------------------------------------------------------------
