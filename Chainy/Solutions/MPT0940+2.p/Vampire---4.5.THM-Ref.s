%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0940+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 240 expanded)
%              Number of leaves         :    9 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 (1214 expanded)
%              Number of equality atoms :   48 ( 234 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4229,plain,(
    $false ),
    inference(global_subsumption,[],[f2088,f2232,f2315,f4228])).

fof(f4228,plain,(
    ~ r1_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) ),
    inference(subsumption_resolution,[],[f4227,f1924])).

fof(f1924,plain,(
    sK1(k1_wellord2(sK0)) != sK2(k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1674,f1660,f1665])).

fof(f1665,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1532])).

fof(f1532,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK1(X0) != sK2(X0)
            & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f1530,f1531])).

fof(f1531,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK1(X0) != sK2(X0)
        & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1530,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1529])).

fof(f1529,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1438])).

fof(f1438,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1437])).

fof(f1437,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1149])).

fof(f1149,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

fof(f1660,plain,(
    ~ v4_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f1528])).

fof(f1528,plain,(
    ~ v4_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1434,f1527])).

fof(f1527,plain,
    ( ? [X0] : ~ v4_relat_2(k1_wellord2(X0))
   => ~ v4_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f1434,plain,(
    ? [X0] : ~ v4_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f1430])).

fof(f1430,negated_conjecture,(
    ~ ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f1429])).

fof(f1429,conjecture,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

fof(f1674,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1423,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f4227,plain,
    ( sK1(k1_wellord2(sK0)) = sK2(k1_wellord2(sK0))
    | ~ r1_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) ),
    inference(subsumption_resolution,[],[f4226,f2232])).

fof(f4226,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | sK1(k1_wellord2(sK0)) = sK2(k1_wellord2(sK0))
    | ~ r1_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) ),
    inference(subsumption_resolution,[],[f4223,f2315])).

fof(f4223,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | sK1(k1_wellord2(sK0)) = sK2(k1_wellord2(sK0))
    | ~ r1_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) ),
    inference(resolution,[],[f2006,f1794])).

fof(f1794,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1621])).

fof(f1621,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1620])).

fof(f1620,plain,(
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

fof(f2006,plain,
    ( r1_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f1984,f1674])).

fof(f1984,plain,
    ( r1_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f1922,f1853])).

fof(f1853,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1667])).

fof(f1667,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1537])).

fof(f1537,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f1535,f1536])).

fof(f1536,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1535,plain,(
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
    inference(rectify,[],[f1534])).

fof(f1534,plain,(
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
    inference(flattening,[],[f1533])).

fof(f1533,plain,(
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
    inference(nnf_transformation,[],[f1440])).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1439])).

fof(f1439,plain,(
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

fof(f1922,plain,(
    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0))),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1674,f1660,f1663])).

fof(f1663,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1532])).

fof(f2315,plain,(
    r2_hidden(sK2(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f2306,f1674])).

% (7953)Refutation not found, incomplete strategy% (7953)------------------------------
% (7953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f2306,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f1942,f1854])).

fof(f1854,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1666])).

fof(f1666,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1537])).

fof(f1942,plain,(
    r2_hidden(sK2(k1_wellord2(sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f1674,f1922,f1797])).

fof(f1797,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1496])).

fof(f1496,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1495])).

fof(f1495,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f2232,plain,(
    r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f2223,f1674])).

fof(f2223,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f1941,f1854])).

fof(f1941,plain,(
    r2_hidden(sK1(k1_wellord2(sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f1674,f1922,f1796])).

fof(f1796,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1496])).

fof(f2088,plain,
    ( r1_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f2066,f1674])).

fof(f2066,plain,
    ( r1_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f1923,f1853])).

fof(f1923,plain,(
    r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f1674,f1660,f1664])).

fof(f1664,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1532])).
%------------------------------------------------------------------------------
