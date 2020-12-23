%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0662+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 133 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 ( 532 expanded)
%              Number of equality atoms :   33 ( 104 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6521,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6512,f1620])).

fof(f1620,plain,(
    ~ r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2) ),
    inference(subsumption_resolution,[],[f1619,f1147])).

fof(f1147,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1082])).

fof(f1082,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f971,f1081])).

fof(f1081,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f971,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f970])).

fof(f970,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f966])).

fof(f966,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f965])).

fof(f965,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f1619,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1618,f1148])).

fof(f1148,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1082])).

fof(f1618,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1610,f1591])).

fof(f1591,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1573,f1147])).

fof(f1573,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1149,f1224])).

fof(f1224,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1132])).

fof(f1132,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1131])).

fof(f1131,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1017])).

fof(f1017,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f875])).

fof(f875,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f1149,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f1082])).

fof(f1610,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1317,f1343])).

fof(f1343,plain,(
    ! [X2,X0,X1] :
      ( sQ27_eqProxy(k1_funct_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1195,f1316])).

fof(f1316,plain,(
    ! [X1,X0] :
      ( sQ27_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ27_eqProxy])])).

fof(f1195,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1108])).

fof(f1108,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1001])).

fof(f1001,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1000])).

fof(f1000,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f891])).

fof(f891,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f1317,plain,(
    ~ sQ27_eqProxy(k1_funct_1(sK2,sK0),k1_funct_1(k7_relat_1(sK2,sK1),sK0)) ),
    inference(equality_proxy_replacement,[],[f1150,f1316])).

fof(f1150,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f1082])).

fof(f6512,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2) ),
    inference(resolution,[],[f1812,f1600])).

fof(f1600,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f1599,f1505])).

fof(f1505,plain,(
    ! [X38] : v1_relat_1(k7_relat_1(sK2,X38)) ),
    inference(subsumption_resolution,[],[f1430,f1148])).

fof(f1430,plain,(
    ! [X38] :
      ( v1_relat_1(k7_relat_1(sK2,X38))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f1147,f1235])).

fof(f1235,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1032])).

fof(f1032,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1031])).

fof(f1031,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f908])).

fof(f908,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f1599,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f1578,f1506])).

fof(f1506,plain,(
    ! [X39] : v1_funct_1(k7_relat_1(sK2,X39)) ),
    inference(subsumption_resolution,[],[f1431,f1148])).

fof(f1431,plain,(
    ! [X39] :
      ( v1_funct_1(k7_relat_1(sK2,X39))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f1147,f1236])).

fof(f1236,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1032])).

fof(f1578,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f1149,f1300])).

fof(f1300,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f1156])).

fof(f1156,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1086])).

fof(f1086,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1085])).

fof(f1085,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f975])).

fof(f975,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f974])).

fof(f974,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f967])).

fof(f967,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f1812,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_relat_1(sK2,X1))
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f1445,f1214])).

fof(f1214,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1127,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f1125,f1126])).

fof(f1126,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1125,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1124])).

fof(f1124,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1009])).

fof(f1009,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1445,plain,(
    ! [X61] : r1_tarski(k7_relat_1(sK2,X61),sK2) ),
    inference(resolution,[],[f1147,f1255])).

fof(f1255,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1055])).

fof(f1055,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f877])).

fof(f877,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
%------------------------------------------------------------------------------
