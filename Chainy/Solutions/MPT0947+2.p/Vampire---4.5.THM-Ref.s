%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0947+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 179 expanded)
%              Number of leaves         :   10 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 ( 979 expanded)
%              Number of equality atoms :   17 ( 139 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2436,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2413,f1534])).

fof(f1534,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1492])).

fof(f1492,plain,
    ( sK2 != sK3
    & r4_wellord1(sK1,k1_wellord2(sK3))
    & r4_wellord1(sK1,k1_wellord2(sK2))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f1448,f1491,f1490,f1489])).

fof(f1489,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r4_wellord1(X0,k1_wellord2(X2))
                & r4_wellord1(X0,k1_wellord2(X1))
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(sK1,k1_wellord2(X2))
              & r4_wellord1(sK1,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1490,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r4_wellord1(sK1,k1_wellord2(X2))
            & r4_wellord1(sK1,k1_wellord2(X1))
            & v3_ordinal1(X2) )
        & v3_ordinal1(X1) )
   => ( ? [X2] :
          ( sK2 != X2
          & r4_wellord1(sK1,k1_wellord2(X2))
          & r4_wellord1(sK1,k1_wellord2(sK2))
          & v3_ordinal1(X2) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1491,plain,
    ( ? [X2] :
        ( sK2 != X2
        & r4_wellord1(sK1,k1_wellord2(X2))
        & r4_wellord1(sK1,k1_wellord2(sK2))
        & v3_ordinal1(X2) )
   => ( sK2 != sK3
      & r4_wellord1(sK1,k1_wellord2(sK3))
      & r4_wellord1(sK1,k1_wellord2(sK2))
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1448,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1447])).

fof(f1447,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1432])).

fof(f1432,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r4_wellord1(X0,k1_wellord2(X2))
                    & r4_wellord1(X0,k1_wellord2(X1)) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1431])).

fof(f1431,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r4_wellord1(X0,k1_wellord2(X2))
                  & r4_wellord1(X0,k1_wellord2(X1)) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord2)).

fof(f2413,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f2310,f1658])).

fof(f1658,plain,(
    r4_wellord1(sK1,sK1) ),
    inference(resolution,[],[f1534,f1567])).

fof(f1567,plain,(
    ! [X0] :
      ( r4_wellord1(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1469])).

fof(f1469,plain,(
    ! [X0] :
      ( r4_wellord1(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1190])).

fof(f1190,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r4_wellord1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_wellord1)).

fof(f2310,plain,(
    ! [X1] :
      ( ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f2309,f1889])).

fof(f1889,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(k1_wellord2(sK2),X0) ) ),
    inference(global_subsumption,[],[f1655,f1690,f1710,f1888])).

fof(f1888,plain,(
    ! [X0] :
      ( ~ r4_wellord1(X0,k1_wellord2(sK3))
      | ~ r4_wellord1(k1_wellord2(sK2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1887,f1580])).

fof(f1580,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1423,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1887,plain,(
    ! [X0] :
      ( ~ r4_wellord1(X0,k1_wellord2(sK3))
      | ~ r4_wellord1(k1_wellord2(sK2),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_wellord2(sK2)) ) ),
    inference(subsumption_resolution,[],[f1868,f1580])).

fof(f1868,plain,(
    ! [X0] :
      ( ~ r4_wellord1(X0,k1_wellord2(sK3))
      | ~ r4_wellord1(k1_wellord2(sK2),X0)
      | ~ v1_relat_1(k1_wellord2(sK3))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_wellord2(sK2)) ) ),
    inference(resolution,[],[f1682,f1559])).

fof(f1559,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1460])).

fof(f1460,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1459])).

fof(f1459,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1194])).

fof(f1194,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

fof(f1682,plain,(
    ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(subsumption_resolution,[],[f1681,f1535])).

fof(f1535,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f1492])).

fof(f1681,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v3_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f1677,f1536])).

fof(f1536,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f1492])).

fof(f1677,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f1605,f1614])).

fof(f1614,plain,(
    ! [X0,X1] :
      ( sQ22_eqProxy(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1577,f1604])).

fof(f1604,plain,(
    ! [X1,X0] :
      ( sQ22_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ22_eqProxy])])).

fof(f1577,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1475])).

fof(f1475,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1474])).

fof(f1474,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1430])).

fof(f1430,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f1605,plain,(
    ~ sQ22_eqProxy(sK2,sK3) ),
    inference(equality_proxy_replacement,[],[f1539,f1604])).

fof(f1539,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f1492])).

fof(f1710,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK3))
      | ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f1709,f1534])).

fof(f1709,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK3))
      | ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f1704,f1580])).

fof(f1704,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK3))
      | ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(k1_wellord2(sK3))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f1538,f1559])).

fof(f1538,plain,(
    r4_wellord1(sK1,k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f1492])).

fof(f1690,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k1_wellord2(sK2),X0)
      | r4_wellord1(sK1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1689,f1534])).

fof(f1689,plain,(
    ! [X0] :
      ( r4_wellord1(sK1,X0)
      | ~ r4_wellord1(k1_wellord2(sK2),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1685,f1580])).

fof(f1685,plain,(
    ! [X0] :
      ( r4_wellord1(sK1,X0)
      | ~ r4_wellord1(k1_wellord2(sK2),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_wellord2(sK2))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1537,f1559])).

fof(f1537,plain,(
    r4_wellord1(sK1,k1_wellord2(sK2)) ),
    inference(cnf_transformation,[],[f1492])).

fof(f1655,plain,(
    ! [X78] :
      ( r4_wellord1(X78,sK1)
      | ~ r4_wellord1(sK1,X78)
      | ~ v1_relat_1(X78) ) ),
    inference(resolution,[],[f1534,f1565])).

fof(f1565,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1466])).

fof(f1466,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1465])).

fof(f1465,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1192])).

fof(f1192,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f2309,plain,(
    ! [X1] :
      ( ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(X1)
      | r4_wellord1(k1_wellord2(sK2),X1) ) ),
    inference(subsumption_resolution,[],[f2305,f1580])).

fof(f2305,plain,(
    ! [X1] :
      ( ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(X1)
      | r4_wellord1(k1_wellord2(sK2),X1)
      | ~ v1_relat_1(k1_wellord2(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f2298])).

fof(f2298,plain,(
    ! [X1] :
      ( ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(X1)
      | r4_wellord1(k1_wellord2(sK2),X1)
      | ~ v1_relat_1(k1_wellord2(sK2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f1692,f1565])).

fof(f1692,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK2))
      | ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f1691,f1534])).

fof(f1691,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK2))
      | ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f1686,f1580])).

fof(f1686,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK2))
      | ~ r4_wellord1(X1,sK1)
      | ~ v1_relat_1(k1_wellord2(sK2))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f1537,f1559])).
%------------------------------------------------------------------------------
