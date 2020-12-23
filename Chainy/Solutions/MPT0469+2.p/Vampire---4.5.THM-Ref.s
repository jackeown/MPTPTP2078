%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0469+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 209 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3795,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3746,f3782,f3793])).

fof(f3793,plain,(
    spl143_1 ),
    inference(avatar_contradiction_clause,[],[f3792])).

fof(f3792,plain,
    ( $false
    | spl143_1 ),
    inference(subsumption_resolution,[],[f3788,f3741])).

fof(f3741,plain,
    ( ~ sQ142_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | spl143_1 ),
    inference(avatar_component_clause,[],[f3739])).

fof(f3739,plain,
    ( spl143_1
  <=> sQ142_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl143_1])])).

fof(f3788,plain,(
    sQ142_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f3758,f2981])).

fof(f2981,plain,(
    ! [X0] :
      ( r2_hidden(sK23(X0),X0)
      | sQ142_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f1745,f2906])).

fof(f2906,plain,(
    ! [X1,X0] :
      ( sQ142_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ142_eqProxy])])).

fof(f1745,plain,(
    ! [X0] :
      ( r2_hidden(sK23(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1255])).

fof(f1255,plain,(
    ! [X0] :
      ( r2_hidden(sK23(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f802,f1254])).

fof(f1254,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK23(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f802,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f3758,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f3752,f2737])).

fof(f2737,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK77(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2086])).

fof(f2086,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK77(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1404])).

fof(f1404,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK75(X0,X1),X3),X0)
            | ~ r2_hidden(sK75(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK75(X0,X1),sK76(X0,X1)),X0)
            | r2_hidden(sK75(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK77(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK75,sK76,sK77])],[f1400,f1403,f1402,f1401])).

fof(f1401,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK75(X0,X1),X3),X0)
          | ~ r2_hidden(sK75(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK75(X0,X1),X4),X0)
          | r2_hidden(sK75(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1402,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK75(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK75(X0,X1),sK76(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1403,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK77(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1400,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1399])).

fof(f1399,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f3752,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f1743,f1608])).

fof(f1608,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1743,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1253])).

fof(f1253,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK22(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f1251,f1252])).

fof(f1252,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK22(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1251,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1250])).

fof(f1250,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f3782,plain,(
    spl143_2 ),
    inference(avatar_contradiction_clause,[],[f3781])).

fof(f3781,plain,
    ( $false
    | spl143_2 ),
    inference(subsumption_resolution,[],[f3777,f3745])).

fof(f3745,plain,
    ( ~ sQ142_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | spl143_2 ),
    inference(avatar_component_clause,[],[f3743])).

fof(f3743,plain,
    ( spl143_2
  <=> sQ142_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl143_2])])).

fof(f3777,plain,(
    sQ142_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f3757,f2981])).

fof(f3757,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f3752,f2735])).

fof(f2735,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK74(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2082])).

fof(f2082,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK74(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1398])).

fof(f1398,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK72(X0,X1)),X0)
            | ~ r2_hidden(sK72(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK73(X0,X1),sK72(X0,X1)),X0)
            | r2_hidden(sK72(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK74(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK72,sK73,sK74])],[f1394,f1397,f1396,f1395])).

fof(f1395,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK72(X0,X1)),X0)
          | ~ r2_hidden(sK72(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK72(X0,X1)),X0)
          | r2_hidden(sK72(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1396,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK72(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK73(X0,X1),sK72(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1397,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK74(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1394,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1393])).

fof(f1393,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f3746,plain,
    ( ~ spl143_1
    | ~ spl143_2 ),
    inference(avatar_split_clause,[],[f2924,f3743,f3739])).

fof(f2924,plain,
    ( ~ sQ142_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ sQ142_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f1606,f2906,f2906])).

fof(f1606,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f719])).

fof(f719,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f702])).

fof(f702,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f701])).

fof(f701,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
