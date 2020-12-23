%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0492+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 2.94s
% Output     : Refutation 2.94s
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
fof(f5825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4547,f5506,f5824])).

fof(f5824,plain,
    ( ~ spl150_3
    | ~ spl150_4 ),
    inference(avatar_contradiction_clause,[],[f5823])).

fof(f5823,plain,
    ( $false
    | ~ spl150_3
    | ~ spl150_4 ),
    inference(unit_resulting_resolution,[],[f5508,f5518,f2897])).

fof(f2897,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK87(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f2233])).

fof(f2233,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK87(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1493])).

fof(f1493,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK85(X0,X1),X3),X0)
            | ~ r2_hidden(sK85(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK85(X0,X1),sK86(X0,X1)),X0)
            | r2_hidden(sK85(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK87(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK85,sK86,sK87])],[f1489,f1492,f1491,f1490])).

fof(f1490,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK85(X0,X1),X3),X0)
          | ~ r2_hidden(sK85(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK85(X0,X1),X4),X0)
          | r2_hidden(sK85(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1491,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK85(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK85(X0,X1),sK86(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1492,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK87(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1489,plain,(
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
    inference(rectify,[],[f1488])).

fof(f1488,plain,(
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
    inference(nnf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f5518,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),X0),sK4)
    | ~ spl150_3
    | ~ spl150_4 ),
    inference(subsumption_resolution,[],[f5517,f1695])).

fof(f1695,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1286])).

fof(f1286,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != k3_xboole_0(k1_relat_1(sK4),sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f752,f1285])).

fof(f1285,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK4,sK3)) != k3_xboole_0(k1_relat_1(sK4),sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f752,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f735])).

fof(f735,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f734])).

fof(f734,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f5517,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),X0),sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl150_3
    | ~ spl150_4 ),
    inference(subsumption_resolution,[],[f5516,f5509])).

fof(f5509,plain,
    ( r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),sK3)
    | ~ spl150_3 ),
    inference(resolution,[],[f4542,f2944])).

fof(f2944,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2495])).

fof(f2495,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f1584,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK122(X0,X1,X2),X1)
            | ~ r2_hidden(sK122(X0,X1,X2),X0)
            | ~ r2_hidden(sK122(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK122(X0,X1,X2),X1)
              & r2_hidden(sK122(X0,X1,X2),X0) )
            | r2_hidden(sK122(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK122])],[f1582,f1583])).

fof(f1583,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK122(X0,X1,X2),X1)
          | ~ r2_hidden(sK122(X0,X1,X2),X0)
          | ~ r2_hidden(sK122(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK122(X0,X1,X2),X1)
            & r2_hidden(sK122(X0,X1,X2),X0) )
          | r2_hidden(sK122(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1582,plain,(
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
    inference(rectify,[],[f1581])).

fof(f1581,plain,(
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
    inference(flattening,[],[f1580])).

fof(f1580,plain,(
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

fof(f4542,plain,
    ( r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k3_xboole_0(k1_relat_1(sK4),sK3))
    | ~ spl150_3 ),
    inference(avatar_component_clause,[],[f4541])).

fof(f4541,plain,
    ( spl150_3
  <=> r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl150_3])])).

fof(f5516,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),X0),sK4)
        | ~ r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),sK3)
        | ~ v1_relat_1(sK4) )
    | ~ spl150_4 ),
    inference(resolution,[],[f4546,f3950])).

fof(f3950,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2867,f1980])).

fof(f1980,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f860])).

fof(f860,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2867,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1835])).

fof(f1835,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1320])).

fof(f1320,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK21(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X0)
                    & r2_hidden(sK21(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22])],[f1318,f1319])).

fof(f1319,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X0)
          | ~ r2_hidden(sK21(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X0)
            & r2_hidden(sK21(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK21(X0,X1,X2),sK22(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1318,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1317])).

fof(f1317,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1316])).

fof(f1316,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f822])).

fof(f822,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f4546,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),X0),k7_relat_1(sK4,sK3))
    | ~ spl150_4 ),
    inference(avatar_component_clause,[],[f4545])).

fof(f4545,plain,
    ( spl150_4
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),X0),k7_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl150_4])])).

fof(f5508,plain,
    ( r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k1_relat_1(sK4))
    | ~ spl150_3 ),
    inference(resolution,[],[f4542,f2945])).

fof(f2945,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2494])).

fof(f2494,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f5506,plain,(
    spl150_3 ),
    inference(avatar_contradiction_clause,[],[f5500])).

fof(f5500,plain,
    ( $false
    | spl150_3 ),
    inference(unit_resulting_resolution,[],[f5129,f4543,f5127,f2943])).

fof(f2943,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2496])).

fof(f2496,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f5127,plain,
    ( r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k1_relat_1(sK4))
    | spl150_3 ),
    inference(subsumption_resolution,[],[f5120,f1695])).

fof(f5120,plain,
    ( ~ v1_relat_1(sK4)
    | r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k1_relat_1(sK4))
    | spl150_3 ),
    inference(resolution,[],[f5110,f3942])).

fof(f3942,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X1,X3))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f2359,f2896])).

fof(f2896,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2234])).

fof(f2234,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1493])).

fof(f2359,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1532])).

fof(f1532,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1531])).

fof(f1531,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1091])).

fof(f1091,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f730])).

fof(f730,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f5110,plain,
    ( r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),sK86(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3))),k7_relat_1(sK4,sK3))
    | spl150_3 ),
    inference(subsumption_resolution,[],[f3949,f4543])).

fof(f3949,plain,
    ( r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),sK86(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3))),k7_relat_1(sK4,sK3))
    | r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(resolution,[],[f3355,f3081])).

fof(f3081,plain,(
    ~ sQ149_eqProxy(k1_relat_1(k7_relat_1(sK4,sK3)),k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(equality_proxy_replacement,[],[f1696,f3063])).

fof(f3063,plain,(
    ! [X1,X0] :
      ( sQ149_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ149_eqProxy])])).

fof(f1696,plain,(
    k1_relat_1(k7_relat_1(sK4,sK3)) != k3_xboole_0(k1_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f1286])).

fof(f3355,plain,(
    ! [X0,X1] :
      ( sQ149_eqProxy(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK85(X0,X1),sK86(X0,X1)),X0)
      | r2_hidden(sK85(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f2235,f3063])).

fof(f2235,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK85(X0,X1),sK86(X0,X1)),X0)
      | r2_hidden(sK85(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1493])).

fof(f4543,plain,
    ( ~ r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k3_xboole_0(k1_relat_1(sK4),sK3))
    | spl150_3 ),
    inference(avatar_component_clause,[],[f4541])).

fof(f5129,plain,
    ( r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),sK3)
    | spl150_3 ),
    inference(subsumption_resolution,[],[f5122,f1695])).

fof(f5122,plain,
    ( r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),sK3)
    | ~ v1_relat_1(sK4)
    | spl150_3 ),
    inference(resolution,[],[f5110,f3944])).

fof(f3944,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2869,f1980])).

fof(f2869,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1833])).

fof(f1833,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1320])).

fof(f4547,plain,
    ( ~ spl150_3
    | spl150_4 ),
    inference(avatar_split_clause,[],[f3945,f4545,f4541])).

fof(f3945,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),X0),k7_relat_1(sK4,sK3))
      | ~ r2_hidden(sK85(k7_relat_1(sK4,sK3),k3_xboole_0(k1_relat_1(sK4),sK3)),k3_xboole_0(k1_relat_1(sK4),sK3)) ) ),
    inference(resolution,[],[f3354,f3081])).

fof(f3354,plain,(
    ! [X0,X3,X1] :
      ( sQ149_eqProxy(k1_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK85(X0,X1),X3),X0)
      | ~ r2_hidden(sK85(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f2236,f3063])).

fof(f2236,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK85(X0,X1),X3),X0)
      | ~ r2_hidden(sK85(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1493])).
%------------------------------------------------------------------------------
