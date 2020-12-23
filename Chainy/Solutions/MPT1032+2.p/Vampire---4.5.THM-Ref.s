%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1032+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 231 expanded)
%              Number of leaves         :   13 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  381 (1603 expanded)
%              Number of equality atoms :   98 ( 453 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2376,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2375,f2052])).

fof(f2052,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1830])).

fof(f1830,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1746])).

fof(f1746,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1745])).

fof(f1745,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2375,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f2374,f2356])).

fof(f2356,plain,(
    sK0 = k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2329,f2330])).

fof(f2330,plain,(
    sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) = sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2130,f2067])).

fof(f2067,plain,(
    ! [X6,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1849])).

fof(f1849,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1758])).

fof(f1758,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
              & k1_relat_1(sK7(X0,X1,X2)) = X0
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
                & k1_relat_1(sK8(X0,X1,X6)) = X0
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f1754,f1757,f1756,f1755])).

fof(f1755,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1756,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK6(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
        & k1_relat_1(sK7(X0,X1,X2)) = X0
        & sK6(X0,X1,X2) = sK7(X0,X1,X2)
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1757,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
        & k1_relat_1(sK8(X0,X1,X6)) = X0
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1754,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1753])).

fof(f1753,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1477])).

fof(f1477,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f2130,plain,(
    r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1824,f1828])).

fof(f1828,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1744])).

fof(f1744,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1742,f1743])).

fof(f1743,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1742,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1741])).

fof(f1741,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1598])).

fof(f1598,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1824,plain,(
    ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1740])).

fof(f1740,plain,(
    ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1594,f1739])).

fof(f1739,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))
   => ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f1594,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(ennf_transformation,[],[f1530])).

fof(f1530,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(negated_conjecture,[],[f1529])).

fof(f1529,conjecture,(
    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_2)).

fof(f2329,plain,(
    sK0 = k1_relat_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f2130,f2066])).

fof(f2066,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1850])).

fof(f1850,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1758])).

fof(f2374,plain,(
    ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f2373,f2355])).

fof(f2355,plain,(
    v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2332,f2330])).

fof(f2332,plain,(
    v1_relat_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f2130,f2069])).

fof(f2069,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1847])).

fof(f1847,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1758])).

fof(f2373,plain,
    ( ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2372,f2354])).

fof(f2354,plain,(
    v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2331,f2330])).

fof(f2331,plain,(
    v1_funct_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f2130,f2068])).

fof(f2068,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1848])).

fof(f1848,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1758])).

fof(f2372,plain,
    ( ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))
    | ~ v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2371,f2357])).

fof(f2357,plain,(
    r1_tarski(k2_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK1) ),
    inference(forward_demodulation,[],[f2328,f2330])).

fof(f2328,plain,(
    r1_tarski(k2_relat_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),sK1) ),
    inference(unit_resulting_resolution,[],[f2130,f2065])).

fof(f2065,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1851])).

fof(f1851,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1758])).

fof(f2371,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK1)
    | ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))
    | ~ v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(resolution,[],[f2131,f2055])).

fof(f2055,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(X7,k4_partfun1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ r1_tarski(k1_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(equality_resolution,[],[f2054])).

fof(f2054,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ r1_tarski(k1_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f1838])).

fof(f1838,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ r1_tarski(k1_relat_1(X7),X0)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1752])).

fof(f1752,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | ~ r1_tarski(k1_relat_1(X4),X0)
                | sK3(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1)
              & r1_tarski(k1_relat_1(sK4(X0,X1,X2)),X0)
              & sK3(X0,X1,X2) = sK4(X0,X1,X2)
              & v1_funct_1(sK4(X0,X1,X2))
              & v1_relat_1(sK4(X0,X1,X2)) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | ~ r1_tarski(k1_relat_1(X7),X0)
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
                & r1_tarski(k1_relat_1(sK5(X0,X1,X6)),X0)
                & sK5(X0,X1,X6) = X6
                & v1_funct_1(sK5(X0,X1,X6))
                & v1_relat_1(sK5(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f1748,f1751,f1750,f1749])).

fof(f1749,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | ~ r1_tarski(k1_relat_1(X4),X0)
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & r1_tarski(k1_relat_1(X5),X0)
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | ~ r1_tarski(k1_relat_1(X4),X0)
              | sK3(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & r1_tarski(k1_relat_1(X5),X0)
              & sK3(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1750,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & r1_tarski(k1_relat_1(X5),X0)
          & sK3(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1)
        & r1_tarski(k1_relat_1(sK4(X0,X1,X2)),X0)
        & sK3(X0,X1,X2) = sK4(X0,X1,X2)
        & v1_funct_1(sK4(X0,X1,X2))
        & v1_relat_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1751,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & r1_tarski(k1_relat_1(X8),X0)
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
        & r1_tarski(k1_relat_1(sK5(X0,X1,X6)),X0)
        & sK5(X0,X1,X6) = X6
        & v1_funct_1(sK5(X0,X1,X6))
        & v1_relat_1(sK5(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1748,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & r1_tarski(k1_relat_1(X5),X0)
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | ~ r1_tarski(k1_relat_1(X7),X0)
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & r1_tarski(k1_relat_1(X8),X0)
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1747])).

fof(f1747,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & r1_tarski(k1_relat_1(X4),X0)
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & r1_tarski(k1_relat_1(X4),X0)
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1480])).

fof(f1480,axiom,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & r1_tarski(k1_relat_1(X4),X0)
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_partfun1)).

fof(f2131,plain,(
    ~ r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k4_partfun1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1824,f1829])).

fof(f1829,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1744])).
%------------------------------------------------------------------------------
