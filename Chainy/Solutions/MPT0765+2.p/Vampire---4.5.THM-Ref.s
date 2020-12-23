%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0765+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 305 expanded)
%              Number of leaves         :    9 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          :  214 (1581 expanded)
%              Number of equality atoms :   15 ( 185 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2529,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2522,f1784])).

fof(f1784,plain,(
    r2_hidden(sK31(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1783,f1251])).

fof(f1251,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1194])).

fof(f1194,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
          & r2_hidden(sK1(X1),k3_relat_1(sK0)) )
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    & k1_xboole_0 != k3_relat_1(sK0)
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1152,f1193,f1192])).

fof(f1192,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k1_xboole_0 != k3_relat_1(X0)
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
              & r2_hidden(X2,k3_relat_1(sK0)) )
          | ~ r2_hidden(X1,k3_relat_1(sK0)) )
      & k1_xboole_0 != k3_relat_1(sK0)
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1193,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
          & r2_hidden(X2,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        & r2_hidden(sK1(X1),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1152,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k1_xboole_0 != k3_relat_1(X0)
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1151])).

fof(f1151,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k1_xboole_0 != k3_relat_1(X0)
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1143])).

fof(f1143,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k1_xboole_0 != k3_relat_1(X0)
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f1142])).

fof(f1142,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k1_xboole_0 != k3_relat_1(X0)
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

fof(f1783,plain,
    ( r2_hidden(sK31(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1782,f1252])).

fof(f1252,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f1194])).

fof(f1782,plain,
    ( r2_hidden(sK31(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1775,f1353])).

fof(f1353,plain,(
    ~ sQ32_eqProxy(k1_xboole_0,k3_relat_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f1253,f1352])).

fof(f1352,plain,(
    ! [X1,X0] :
      ( sQ32_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ32_eqProxy])])).

fof(f1253,plain,(
    k1_xboole_0 != k3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1194])).

fof(f1775,plain,
    ( r2_hidden(sK31(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | sQ32_eqProxy(k1_xboole_0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1762,f1396])).

fof(f1396,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK31(X0,X1),X1)
      | sQ32_eqProxy(k1_xboole_0,X1)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1334,f1352])).

fof(f1334,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK31(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1250])).

fof(f1250,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK31(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK31(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31])],[f1191,f1249])).

fof(f1249,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK31(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK31(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1191,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1190])).

fof(f1190,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1141])).

fof(f1141,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f1762,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1755,f1251])).

fof(f1755,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1754,f1406])).

fof(f1406,plain,(
    ! [X13] :
      ( ~ r1_tarski(sK0,X13)
      | r1_tarski(k3_relat_1(sK0),k3_relat_1(X13))
      | ~ v1_relat_1(X13) ) ),
    inference(resolution,[],[f1251,f1323])).

fof(f1323,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1183])).

fof(f1183,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1182])).

fof(f1182,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f834])).

fof(f834,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f1754,plain,(
    r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f1753,f1251])).

fof(f1753,plain,
    ( r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f1740])).

fof(f1740,plain,
    ( r1_tarski(sK0,sK0)
    | r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1403,f1294])).

fof(f1294,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK17(X0,X1),sK18(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1225])).

fof(f1225,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK17(X0,X1),sK18(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK17(X0,X1),sK18(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f1223,f1224])).

fof(f1224,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK17(X0,X1),sK18(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK17(X0,X1),sK18(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1222])).

fof(f1222,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1166])).

fof(f1166,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f655])).

fof(f655,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f1403,plain,(
    ! [X8] :
      ( ~ r2_hidden(k4_tarski(sK17(sK0,X8),sK18(sK0,X8)),X8)
      | r1_tarski(sK0,X8) ) ),
    inference(resolution,[],[f1251,f1295])).

fof(f1295,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK17(X0,X1),sK18(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1225])).

fof(f2522,plain,(
    ~ r2_hidden(sK31(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f2178,f1254])).

fof(f1254,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),k3_relat_1(sK0))
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f1194])).

fof(f2178,plain,(
    ~ r2_hidden(sK1(sK31(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f2177,f1762])).

fof(f2177,plain,
    ( ~ r2_hidden(sK1(sK31(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f2169,f1353])).

fof(f2169,plain,
    ( ~ r2_hidden(sK1(sK31(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | sQ32_eqProxy(k1_xboole_0,k3_relat_1(sK0))
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(resolution,[],[f1518,f1784])).

fof(f1518,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK31(sK0,X0),k3_relat_1(sK0))
      | ~ r2_hidden(sK1(sK31(sK0,X0)),X0)
      | sQ32_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f1517,f1251])).

fof(f1517,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK31(sK0,X0),k3_relat_1(sK0))
      | ~ r2_hidden(sK1(sK31(sK0,X0)),X0)
      | sQ32_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1512,f1252])).

fof(f1512,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK31(sK0,X0),k3_relat_1(sK0))
      | ~ r2_hidden(sK1(sK31(sK0,X0)),X0)
      | sQ32_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ v2_wellord1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1255,f1395])).

fof(f1395,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK31(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | sQ32_eqProxy(k1_xboole_0,X1)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1335,f1352])).

fof(f1335,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK31(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1250])).

fof(f1255,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f1194])).
%------------------------------------------------------------------------------
