%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0743+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   90 (1213 expanded)
%              Number of leaves         :   16 ( 347 expanded)
%              Depth                    :   26
%              Number of atoms          :  259 (4719 expanded)
%              Number of equality atoms :   35 ( 348 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1973,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1972,f1510])).

fof(f1510,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f1408,f1451])).

fof(f1451,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f442])).

fof(f442,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f1408,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1972,plain,(
    ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f1971,f1887])).

fof(f1887,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f1886,f1678])).

fof(f1678,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f1668,f1313])).

fof(f1313,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1118])).

fof(f1118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1668,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f1592,f1467])).

fof(f1467,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k2_tarski(X1,k1_tarski(X1))))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f1290,f1462])).

fof(f1462,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_tarski(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f1297,f1451])).

fof(f1297,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1058])).

fof(f1058,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f1290,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f1201])).

fof(f1201,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f1200])).

fof(f1200,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1074])).

fof(f1074,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f1592,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1591,f1571])).

fof(f1571,plain,(
    v3_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f1278,f1471])).

fof(f1471,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k2_tarski(X0,k1_tarski(X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f1296,f1462])).

fof(f1296,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1109])).

fof(f1109,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1083])).

fof(f1083,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f1278,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1196])).

fof(f1196,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1193,f1195,f1194])).

fof(f1194,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1195,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1193,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1192])).

fof(f1192,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f1096])).

fof(f1096,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1088])).

fof(f1088,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f1087])).

fof(f1087,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f1591,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0))))
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(subsumption_resolution,[],[f1587,f1279])).

fof(f1279,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f1196])).

fof(f1587,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0))))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(resolution,[],[f1463,f1289])).

fof(f1289,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1106])).

fof(f1106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1105])).

fof(f1105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1082])).

fof(f1082,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f1463,plain,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f1281,f1462])).

fof(f1281,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1196])).

fof(f1886,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1885,f1278])).

fof(f1885,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f1880,f1279])).

fof(f1880,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f1765,f1319])).

fof(f1319,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1124])).

fof(f1124,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1123])).

fof(f1123,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1080])).

fof(f1080,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f1765,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1762,f1313])).

fof(f1762,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f1690,f1307])).

fof(f1307,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1115])).

fof(f1115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1093])).

fof(f1093,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1690,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f1601,f1501])).

fof(f1501,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f1399,f1451])).

fof(f1399,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f1166])).

fof(f1166,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1601,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1600,f1571])).

fof(f1600,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(subsumption_resolution,[],[f1598,f1279])).

fof(f1598,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(resolution,[],[f1464,f1282])).

fof(f1282,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1197])).

fof(f1197,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f1098])).

fof(f1098,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1097])).

fof(f1097,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1070])).

fof(f1070,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f1464,plain,
    ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f1280,f1462])).

fof(f1280,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1196])).

fof(f1971,plain,(
    ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(subsumption_resolution,[],[f1970,f1473])).

fof(f1473,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_tarski(X0))) != X0 ),
    inference(definition_unfolding,[],[f1299,f1462])).

fof(f1299,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f1075])).

fof(f1075,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f1970,plain,
    ( sK0 = k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f1969,f1887])).

fof(f1969,plain,
    ( sK1 = k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(subsumption_resolution,[],[f1921,f1959])).

fof(f1959,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(global_subsumption,[],[f1953,f1955])).

fof(f1955,plain,(
    r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK0) ),
    inference(forward_demodulation,[],[f1954,f1887])).

fof(f1954,plain,(
    r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1) ),
    inference(subsumption_resolution,[],[f1890,f1313])).

fof(f1890,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1) ),
    inference(backward_demodulation,[],[f1464,f1887])).

fof(f1953,plain,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK0)
    | ~ r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f1889,f1887])).

fof(f1889,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k1_tarski(sK0))),sK1) ),
    inference(backward_demodulation,[],[f1463,f1887])).

fof(f1921,plain,
    ( r2_hidden(sK0,sK0)
    | sK1 = k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(backward_demodulation,[],[f1692,f1887])).

fof(f1692,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,k1_tarski(sK0)))) ),
    inference(resolution,[],[f1601,f1324])).

fof(f1324,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1216])).

fof(f1216,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1215])).

fof(f1215,plain,(
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
%------------------------------------------------------------------------------
