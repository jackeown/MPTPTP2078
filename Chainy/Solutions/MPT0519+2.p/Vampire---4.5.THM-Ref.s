%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0519+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 4.12s
% Output     : Refutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 180 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  374 ( 896 expanded)
%              Number of equality atoms :   43 ( 137 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6692,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4820,f5606,f6691])).

fof(f6691,plain,
    ( ~ spl152_5
    | ~ spl152_6 ),
    inference(avatar_contradiction_clause,[],[f6690])).

fof(f6690,plain,
    ( $false
    | ~ spl152_5
    | ~ spl152_6 ),
    inference(unit_resulting_resolution,[],[f5608,f5618,f3017])).

fof(f3017,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK86(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f2337])).

fof(f2337,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK86(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1563])).

fof(f1563,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK84(X0,X1)),X0)
            | ~ r2_hidden(sK84(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK85(X0,X1),sK84(X0,X1)),X0)
            | r2_hidden(sK84(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK86(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK84,sK85,sK86])],[f1559,f1562,f1561,f1560])).

fof(f1560,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK84(X0,X1)),X0)
          | ~ r2_hidden(sK84(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK84(X0,X1)),X0)
          | r2_hidden(sK84(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1561,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK84(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK85(X0,X1),sK84(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1562,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK86(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1559,plain,(
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
    inference(rectify,[],[f1558])).

fof(f1558,plain,(
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
    inference(nnf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f5618,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),sK4)
    | ~ spl152_5
    | ~ spl152_6 ),
    inference(subsumption_resolution,[],[f5617,f1773])).

fof(f1773,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1356])).

fof(f1356,plain,
    ( k2_relat_1(k8_relat_1(sK3,sK4)) != k3_xboole_0(k2_relat_1(sK4),sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f783,f1355])).

fof(f1355,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k2_relat_1(k8_relat_1(sK3,sK4)) != k3_xboole_0(k2_relat_1(sK4),sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f783,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f696])).

fof(f696,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f695])).

fof(f695,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f5617,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl152_5
    | ~ spl152_6 ),
    inference(subsumption_resolution,[],[f5616,f5609])).

fof(f5609,plain,
    ( r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),sK3)
    | ~ spl152_5 ),
    inference(resolution,[],[f4815,f3066])).

fof(f3066,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2614])).

fof(f2614,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1662])).

fof(f1662,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK124(X0,X1,X2),X1)
            | ~ r2_hidden(sK124(X0,X1,X2),X0)
            | ~ r2_hidden(sK124(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK124(X0,X1,X2),X1)
              & r2_hidden(sK124(X0,X1,X2),X0) )
            | r2_hidden(sK124(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK124])],[f1660,f1661])).

fof(f1661,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK124(X0,X1,X2),X1)
          | ~ r2_hidden(sK124(X0,X1,X2),X0)
          | ~ r2_hidden(sK124(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK124(X0,X1,X2),X1)
            & r2_hidden(sK124(X0,X1,X2),X0) )
          | r2_hidden(sK124(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1660,plain,(
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
    inference(rectify,[],[f1659])).

fof(f1659,plain,(
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
    inference(flattening,[],[f1658])).

fof(f1658,plain,(
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

fof(f4815,plain,
    ( r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k3_xboole_0(k2_relat_1(sK4),sK3))
    | ~ spl152_5 ),
    inference(avatar_component_clause,[],[f4814])).

fof(f4814,plain,
    ( spl152_5
  <=> r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k3_xboole_0(k2_relat_1(sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl152_5])])).

fof(f5616,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),sK4)
        | ~ r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),sK3)
        | ~ v1_relat_1(sK4) )
    | ~ spl152_6 ),
    inference(resolution,[],[f4819,f4108])).

fof(f4108,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3001,f2061])).

fof(f2061,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f893])).

fof(f893,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f3001,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2100])).

fof(f2100,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1452])).

fof(f1452,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK49(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
                    & r2_hidden(sK49(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK48,sK49])],[f1450,f1451])).

fof(f1451,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
          | ~ r2_hidden(sK49(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
            & r2_hidden(sK49(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1450,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1449])).

fof(f1449,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1448])).

fof(f1448,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f930])).

fof(f930,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f4819,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),k8_relat_1(sK3,sK4))
    | ~ spl152_6 ),
    inference(avatar_component_clause,[],[f4818])).

fof(f4818,plain,
    ( spl152_6
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),k8_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl152_6])])).

fof(f5608,plain,
    ( r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k2_relat_1(sK4))
    | ~ spl152_5 ),
    inference(resolution,[],[f4815,f3067])).

fof(f3067,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2613])).

fof(f2613,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1662])).

fof(f5606,plain,(
    spl152_5 ),
    inference(avatar_contradiction_clause,[],[f5600])).

fof(f5600,plain,
    ( $false
    | spl152_5 ),
    inference(unit_resulting_resolution,[],[f5578,f4816,f5576,f3065])).

fof(f3065,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2615])).

fof(f2615,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1662])).

fof(f5576,plain,
    ( r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k2_relat_1(sK4))
    | spl152_5 ),
    inference(subsumption_resolution,[],[f5569,f1773])).

fof(f5569,plain,
    ( ~ v1_relat_1(sK4)
    | r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k2_relat_1(sK4))
    | spl152_5 ),
    inference(resolution,[],[f5564,f4096])).

fof(f4096,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X3,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f2474,f3016])).

fof(f3016,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2338])).

fof(f2338,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1563])).

fof(f2474,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1608])).

fof(f1608,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1607])).

fof(f1607,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1158])).

fof(f1158,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f691])).

fof(f691,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

fof(f5564,plain,
    ( r2_hidden(k4_tarski(sK85(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),k8_relat_1(sK3,sK4))
    | spl152_5 ),
    inference(subsumption_resolution,[],[f4107,f4816])).

fof(f4107,plain,
    ( r2_hidden(k4_tarski(sK85(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),k8_relat_1(sK3,sK4))
    | r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k3_xboole_0(k2_relat_1(sK4),sK3)) ),
    inference(resolution,[],[f3490,f3203])).

fof(f3203,plain,(
    ~ sQ151_eqProxy(k2_relat_1(k8_relat_1(sK3,sK4)),k3_xboole_0(k2_relat_1(sK4),sK3)) ),
    inference(equality_proxy_replacement,[],[f1774,f3185])).

fof(f3185,plain,(
    ! [X1,X0] :
      ( sQ151_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ151_eqProxy])])).

fof(f1774,plain,(
    k2_relat_1(k8_relat_1(sK3,sK4)) != k3_xboole_0(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f1356])).

fof(f3490,plain,(
    ! [X0,X1] :
      ( sQ151_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK85(X0,X1),sK84(X0,X1)),X0)
      | r2_hidden(sK84(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f2339,f3185])).

fof(f2339,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK85(X0,X1),sK84(X0,X1)),X0)
      | r2_hidden(sK84(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1563])).

fof(f4816,plain,
    ( ~ r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k3_xboole_0(k2_relat_1(sK4),sK3))
    | spl152_5 ),
    inference(avatar_component_clause,[],[f4814])).

fof(f5578,plain,
    ( r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),sK3)
    | spl152_5 ),
    inference(subsumption_resolution,[],[f5571,f1773])).

fof(f5571,plain,
    ( r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),sK3)
    | ~ v1_relat_1(sK4)
    | spl152_5 ),
    inference(resolution,[],[f5564,f4104])).

fof(f4104,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3003,f2061])).

fof(f3003,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2098])).

fof(f2098,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1452])).

fof(f4820,plain,
    ( ~ spl152_5
    | spl152_6 ),
    inference(avatar_split_clause,[],[f4105,f4818,f4814])).

fof(f4105,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3))),k8_relat_1(sK3,sK4))
      | ~ r2_hidden(sK84(k8_relat_1(sK3,sK4),k3_xboole_0(k2_relat_1(sK4),sK3)),k3_xboole_0(k2_relat_1(sK4),sK3)) ) ),
    inference(resolution,[],[f3489,f3203])).

fof(f3489,plain,(
    ! [X0,X3,X1] :
      ( sQ151_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK84(X0,X1)),X0)
      | ~ r2_hidden(sK84(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f2340,f3185])).

fof(f2340,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK84(X0,X1)),X0)
      | ~ r2_hidden(sK84(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1563])).
%------------------------------------------------------------------------------
