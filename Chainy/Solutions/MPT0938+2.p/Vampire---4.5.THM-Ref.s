%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0938+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 6.98s
% Output     : Refutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 330 expanded)
%              Number of leaves         :    9 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 (1703 expanded)
%              Number of equality atoms :   27 ( 219 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10305,f8742])).

fof(f8742,plain,(
    r1_tarski(sK2(k1_wellord2(sK0)),sK3(k1_wellord2(sK0))) ),
    inference(global_subsumption,[],[f1982,f2229,f2524])).

fof(f2524,plain,(
    r2_hidden(sK3(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f2515,f1622])).

fof(f1622,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1422])).

fof(f1422,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f2515,plain,
    ( r2_hidden(sK3(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f1912,f1768])).

fof(f1768,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1615])).

fof(f1615,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1512])).

fof(f1512,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f1510,f1511])).

fof(f1511,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1510,plain,(
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
    inference(rectify,[],[f1509])).

fof(f1509,plain,(
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
    inference(flattening,[],[f1508])).

fof(f1508,plain,(
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
    inference(nnf_transformation,[],[f1435])).

fof(f1435,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1434])).

fof(f1434,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f1912,plain,(
    r2_hidden(sK3(k1_wellord2(sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f1622,f1837,f1744])).

fof(f1744,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1490])).

fof(f1490,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1489])).

fof(f1489,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f833])).

fof(f833,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f1837,plain,(
    r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),sK3(k1_wellord2(sK0))),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1622,f1609,f1613])).

fof(f1613,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f1507,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f1505,f1506])).

fof(f1506,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1505,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1504])).

fof(f1504,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1433])).

fof(f1433,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1432])).

fof(f1432,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1148])).

fof(f1148,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f1609,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f1503])).

fof(f1503,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1429,f1502])).

fof(f1502,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f1429,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f1427])).

fof(f1427,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f1426])).

fof(f1426,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(f2229,plain,(
    r2_hidden(sK2(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f2220,f1622])).

fof(f2220,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f1844,f1768])).

fof(f1844,plain,(
    r2_hidden(sK2(k1_wellord2(sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f1622,f1836,f1744])).

fof(f1836,plain,(
    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0))),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1622,f1609,f1612])).

fof(f1612,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f1982,plain,
    ( r1_tarski(sK2(k1_wellord2(sK0)),sK3(k1_wellord2(sK0)))
    | ~ r2_hidden(sK3(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f1962,f1622])).

fof(f1962,plain,
    ( r1_tarski(sK2(k1_wellord2(sK0)),sK3(k1_wellord2(sK0)))
    | ~ r2_hidden(sK3(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f1837,f1767])).

fof(f1767,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1616])).

fof(f1616,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1512])).

fof(f10305,plain,(
    ~ r1_tarski(sK2(k1_wellord2(sK0)),sK3(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f3908,f8595,f1734])).

fof(f1734,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1485])).

fof(f1485,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1484])).

fof(f1484,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f8595,plain,(
    r1_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0))) ),
    inference(global_subsumption,[],[f1906,f2147,f2229])).

fof(f2147,plain,(
    r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f2138,f1622])).

fof(f2138,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f1843,f1768])).

fof(f1843,plain,(
    r2_hidden(sK1(k1_wellord2(sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f1622,f1836,f1743])).

fof(f1743,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1490])).

fof(f1906,plain,
    ( r1_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f1886,f1622])).

fof(f1886,plain,
    ( r1_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f1836,f1767])).

fof(f3908,plain,(
    ~ r1_tarski(sK1(k1_wellord2(sK0)),sK3(k1_wellord2(sK0))) ),
    inference(global_subsumption,[],[f2002,f2147,f2524])).

fof(f2002,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0)),sK3(k1_wellord2(sK0)))
    | ~ r2_hidden(sK3(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f1997,f1622])).

fof(f1997,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0)),sK3(k1_wellord2(sK0)))
    | ~ r2_hidden(sK3(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f1838,f1766])).

fof(f1766,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1617])).

fof(f1617,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1512])).

fof(f1838,plain,(
    ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),sK3(k1_wellord2(sK0))),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1622,f1609,f1614])).

fof(f1614,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).
%------------------------------------------------------------------------------
