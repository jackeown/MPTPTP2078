%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0937+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   42 (  68 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 346 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1894,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1893,f1611])).

fof(f1611,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1421])).

fof(f1421,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1893,plain,(
    ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f1892,f1870])).

fof(f1870,plain,(
    r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f1861,f1611])).

fof(f1861,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f1820,f1752])).

fof(f1752,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1604])).

fof(f1604,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1506])).

fof(f1506,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f1504,f1505])).

fof(f1505,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1504,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1503])).

fof(f1503,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1502])).

fof(f1502,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1432])).

fof(f1432,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1431])).

fof(f1431,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1420])).

fof(f1420,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f1820,plain,(
    r2_hidden(sK1(k1_wellord2(sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f1611,f1599,f1602])).

fof(f1602,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_relat_1(X0))
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1501])).

fof(f1501,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f1499,f1500])).

fof(f1500,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1499,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1498])).

fof(f1498,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1146])).

fof(f1146,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(f1599,plain,(
    ~ v1_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f1497])).

fof(f1497,plain,(
    ~ v1_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1427,f1496])).

fof(f1496,plain,
    ( ? [X0] : ~ v1_relat_2(k1_wellord2(X0))
   => ~ v1_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f1427,plain,(
    ? [X0] : ~ v1_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f1425])).

fof(f1425,negated_conjecture,(
    ~ ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f1424])).

fof(f1424,conjecture,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(f1892,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f1890,f1771])).

fof(f1771,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1743])).

fof(f1743,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1598])).

fof(f1598,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1597])).

fof(f1597,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1890,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(duplicate_literal_removal,[],[f1886])).

fof(f1886,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f1821,f1750])).

fof(f1750,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1606])).

fof(f1606,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1506])).

fof(f1821,plain,(
    ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1611,f1599,f1603])).

fof(f1603,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1501])).
%------------------------------------------------------------------------------
