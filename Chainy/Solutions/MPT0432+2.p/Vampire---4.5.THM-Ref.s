%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0432+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 12.08s
% Output     : Refutation 12.08s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 164 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  246 ( 912 expanded)
%              Number of equality atoms :   33 ( 130 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3657,f4957,f5013,f5016,f5030])).

fof(f5030,plain,
    ( ~ spl124_4
    | ~ spl124_6 ),
    inference(avatar_contradiction_clause,[],[f5028])).

fof(f5028,plain,
    ( $false
    | ~ spl124_4
    | ~ spl124_6 ),
    inference(unit_resulting_resolution,[],[f4971,f5012,f2490])).

fof(f2490,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK59(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1859])).

fof(f1859,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK59(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f1247,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK57(X0,X1),X3),X0)
            | ~ r2_hidden(sK57(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK57(X0,X1),sK58(X0,X1)),X0)
            | r2_hidden(sK57(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK59(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK57,sK58,sK59])],[f1243,f1246,f1245,f1244])).

fof(f1244,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK57(X0,X1),X3),X0)
          | ~ r2_hidden(sK57(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK57(X0,X1),X4),X0)
          | r2_hidden(sK57(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1245,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK57(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK57(X0,X1),sK58(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1246,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK59(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1243,plain,(
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
    inference(rectify,[],[f1242])).

fof(f1242,plain,(
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
    inference(nnf_transformation,[],[f640])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f5012,plain,
    ( r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK3))
    | ~ spl124_6 ),
    inference(avatar_component_clause,[],[f5010])).

fof(f5010,plain,
    ( spl124_6
  <=> r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_6])])).

fof(f4971,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X0),sK3)
    | ~ spl124_4 ),
    inference(resolution,[],[f3656,f2541])).

fof(f2541,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2124])).

fof(f2124,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1347])).

fof(f1347,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK98(X0,X1,X2),X1)
              & ~ r2_hidden(sK98(X0,X1,X2),X0) )
            | ~ r2_hidden(sK98(X0,X1,X2),X2) )
          & ( r2_hidden(sK98(X0,X1,X2),X1)
            | r2_hidden(sK98(X0,X1,X2),X0)
            | r2_hidden(sK98(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK98])],[f1345,f1346])).

fof(f1346,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK98(X0,X1,X2),X1)
            & ~ r2_hidden(sK98(X0,X1,X2),X0) )
          | ~ r2_hidden(sK98(X0,X1,X2),X2) )
        & ( r2_hidden(sK98(X0,X1,X2),X1)
          | r2_hidden(sK98(X0,X1,X2),X0)
          | r2_hidden(sK98(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1345,plain,(
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
    inference(rectify,[],[f1344])).

fof(f1344,plain,(
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
    inference(flattening,[],[f1343])).

fof(f1343,plain,(
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

fof(f3656,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X0),k2_xboole_0(sK3,sK4))
    | ~ spl124_4 ),
    inference(avatar_component_clause,[],[f3655])).

fof(f3655,plain,
    ( spl124_4
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X0),k2_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_4])])).

fof(f5016,plain,
    ( ~ spl124_4
    | ~ spl124_5 ),
    inference(avatar_contradiction_clause,[],[f5014])).

fof(f5014,plain,
    ( $false
    | ~ spl124_4
    | ~ spl124_5 ),
    inference(unit_resulting_resolution,[],[f4972,f5008,f2490])).

fof(f5008,plain,
    ( r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK4))
    | ~ spl124_5 ),
    inference(avatar_component_clause,[],[f5006])).

fof(f5006,plain,
    ( spl124_5
  <=> r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_5])])).

fof(f4972,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X1),sK4)
    | ~ spl124_4 ),
    inference(resolution,[],[f3656,f2540])).

fof(f2540,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2125])).

fof(f2125,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1347])).

fof(f5013,plain,
    ( spl124_5
    | spl124_6
    | ~ spl124_3 ),
    inference(avatar_split_clause,[],[f4958,f3651,f5010,f5006])).

fof(f3651,plain,
    ( spl124_3
  <=> r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_3])])).

fof(f4958,plain,
    ( r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK3))
    | r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK4))
    | ~ spl124_3 ),
    inference(resolution,[],[f3652,f2542])).

fof(f2542,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2123])).

fof(f2123,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1347])).

fof(f3652,plain,
    ( r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))
    | ~ spl124_3 ),
    inference(avatar_component_clause,[],[f3651])).

fof(f4957,plain,(
    spl124_3 ),
    inference(avatar_contradiction_clause,[],[f4956])).

fof(f4956,plain,
    ( $false
    | spl124_3 ),
    inference(subsumption_resolution,[],[f4955,f3669])).

fof(f3669,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X0),sK4)
    | spl124_3 ),
    inference(resolution,[],[f3660,f2489])).

fof(f2489,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f1860])).

fof(f1860,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f3660,plain,
    ( ~ r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK4))
    | spl124_3 ),
    inference(resolution,[],[f3653,f2540])).

fof(f3653,plain,
    ( ~ r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))
    | spl124_3 ),
    inference(avatar_component_clause,[],[f3651])).

fof(f4955,plain,
    ( r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),sK58(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),sK4)
    | spl124_3 ),
    inference(subsumption_resolution,[],[f4952,f3662])).

fof(f3662,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X0),sK3)
    | spl124_3 ),
    inference(resolution,[],[f3659,f2489])).

fof(f3659,plain,
    ( ~ r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k1_relat_1(sK3))
    | spl124_3 ),
    inference(resolution,[],[f3653,f2541])).

fof(f4952,plain,
    ( r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),sK58(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),sK3)
    | r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),sK58(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),sK4)
    | spl124_3 ),
    inference(resolution,[],[f3661,f2542])).

fof(f3661,plain,
    ( r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),sK58(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k2_xboole_0(sK3,sK4))
    | spl124_3 ),
    inference(subsumption_resolution,[],[f3658,f2673])).

fof(f2673,plain,(
    ~ sQ123_eqProxy(k1_relat_1(k2_xboole_0(sK3,sK4)),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) ),
    inference(equality_proxy_replacement,[],[f1449,f2655])).

fof(f2655,plain,(
    ! [X1,X0] :
      ( sQ123_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ123_eqProxy])])).

fof(f1449,plain,(
    k1_relat_1(k2_xboole_0(sK3,sK4)) != k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f1094])).

fof(f1094,plain,
    ( k1_relat_1(k2_xboole_0(sK3,sK4)) != k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f661,f1093,f1092])).

fof(f1092,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k2_xboole_0(sK3,X1)) != k2_xboole_0(k1_relat_1(sK3),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1093,plain,
    ( ? [X1] :
        ( k1_relat_1(k2_xboole_0(sK3,X1)) != k2_xboole_0(k1_relat_1(sK3),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k2_xboole_0(sK3,sK4)) != k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f661,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f643])).

fof(f643,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f3658,plain,
    ( r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),sK58(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))),k2_xboole_0(sK3,sK4))
    | sQ123_eqProxy(k1_relat_1(k2_xboole_0(sK3,sK4)),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4)))
    | spl124_3 ),
    inference(resolution,[],[f3653,f2887])).

fof(f2887,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK57(X0,X1),X1)
      | r2_hidden(k4_tarski(sK57(X0,X1),sK58(X0,X1)),X0)
      | sQ123_eqProxy(k1_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f1861,f2655])).

fof(f1861,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK57(X0,X1),sK58(X0,X1)),X0)
      | r2_hidden(sK57(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f3657,plain,
    ( ~ spl124_3
    | spl124_4 ),
    inference(avatar_split_clause,[],[f3426,f3655,f3651])).

fof(f3426,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),X0),k2_xboole_0(sK3,sK4))
      | ~ r2_hidden(sK57(k2_xboole_0(sK3,sK4),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))),k2_xboole_0(k1_relat_1(sK3),k1_relat_1(sK4))) ) ),
    inference(resolution,[],[f2886,f2673])).

fof(f2886,plain,(
    ! [X0,X3,X1] :
      ( sQ123_eqProxy(k1_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK57(X0,X1),X3),X0)
      | ~ r2_hidden(sK57(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1862,f2655])).

fof(f1862,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK57(X0,X1),X3),X0)
      | ~ r2_hidden(sK57(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1247])).
%------------------------------------------------------------------------------
