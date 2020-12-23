%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:56 EST 2020

% Result     : Theorem 3.82s
% Output     : Refutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 916 expanded)
%              Number of leaves         :   50 ( 330 expanded)
%              Depth                    :   10
%              Number of atoms          :  749 (2069 expanded)
%              Number of equality atoms :  144 ( 720 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1570,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f140,f146,f160,f227,f289,f317,f433,f452,f553,f558,f624,f679,f682,f693,f696,f716,f786,f806,f816,f822,f844,f849,f867,f876,f904,f914,f917,f944,f947,f969,f974,f979,f980,f1367,f1370,f1373,f1381,f1384,f1387,f1450,f1465,f1473,f1515,f1548,f1551,f1554,f1562,f1566])).

fof(f1566,plain,
    ( spl13_4
    | ~ spl13_10
    | ~ spl13_26 ),
    inference(avatar_contradiction_clause,[],[f1565])).

fof(f1565,plain,
    ( $false
    | spl13_4
    | ~ spl13_10
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1564,f316])).

fof(f316,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl13_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f1564,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl13_4
    | ~ spl13_26 ),
    inference(forward_demodulation,[],[f1563,f1555])).

fof(f1555,plain,
    ( sK0 = sK11(k1_tarski(sK0),k1_relat_1(sK2))
    | ~ spl13_26 ),
    inference(resolution,[],[f861,f110])).

fof(f110,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f861,plain,
    ( r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f860])).

fof(f860,plain,
    ( spl13_26
  <=> r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f1563,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl13_4
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1560,f112])).

fof(f112,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1560,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl13_4
    | ~ spl13_26 ),
    inference(backward_demodulation,[],[f1444,f1555])).

fof(f1444,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | spl13_4 ),
    inference(extensionality_resolution,[],[f82,f139])).

fof(f139,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl13_4
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
      | ~ r2_hidden(sK11(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f1562,plain,
    ( ~ spl13_10
    | ~ spl13_26
    | spl13_27 ),
    inference(avatar_contradiction_clause,[],[f1561])).

fof(f1561,plain,
    ( $false
    | ~ spl13_10
    | ~ spl13_26
    | spl13_27 ),
    inference(subsumption_resolution,[],[f1559,f316])).

fof(f1559,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl13_26
    | spl13_27 ),
    inference(backward_demodulation,[],[f866,f1555])).

fof(f866,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl13_27 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl13_27
  <=> r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f1554,plain,
    ( ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(avatar_contradiction_clause,[],[f1553])).

fof(f1553,plain,
    ( $false
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f1552,f154])).

fof(f154,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f109,f151])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f87,f89])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f87,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f109,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1552,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(forward_demodulation,[],[f1546,f151])).

fof(f1546,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(backward_demodulation,[],[f870,f1537])).

fof(f1537,plain,
    ( sK0 = sK11(k1_tarski(sK0),k1_relat_1(sK2))
    | ~ spl13_2
    | ~ spl13_27 ),
    inference(resolution,[],[f614,f865])).

fof(f865,plain,
    ( r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f864])).

fof(f614,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl13_2 ),
    inference(resolution,[],[f312,f104])).

fof(f104,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f312,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl13_2 ),
    inference(superposition,[],[f119,f130])).

fof(f130,plain,
    ( sK2 = k1_tarski(k4_tarski(sK0,sK1))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl13_2
  <=> sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X0 = X2 ) ),
    inference(backward_demodulation,[],[f90,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f870,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK11(k1_tarski(sK0),k1_relat_1(sK2))))
    | spl13_26 ),
    inference(resolution,[],[f862,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f862,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | spl13_26 ),
    inference(avatar_component_clause,[],[f860])).

fof(f1551,plain,
    ( ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(avatar_contradiction_clause,[],[f1550])).

fof(f1550,plain,
    ( $false
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f1549,f154])).

fof(f1549,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(forward_demodulation,[],[f1545,f151])).

fof(f1545,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(backward_demodulation,[],[f869,f1537])).

fof(f869,plain,
    ( k1_tarski(sK11(k1_tarski(sK0),k1_relat_1(sK2))) = k4_xboole_0(k1_tarski(sK11(k1_tarski(sK0),k1_relat_1(sK2))),k1_tarski(sK0))
    | spl13_26 ),
    inference(resolution,[],[f862,f118])).

fof(f118,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2) ) ),
    inference(forward_demodulation,[],[f117,f101])).

fof(f101,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f117,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f1548,plain,
    ( ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(avatar_contradiction_clause,[],[f1547])).

fof(f1547,plain,
    ( $false
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f1544,f112])).

fof(f1544,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl13_2
    | spl13_26
    | ~ spl13_27 ),
    inference(backward_demodulation,[],[f862,f1537])).

fof(f1515,plain,
    ( spl13_3
    | spl13_23
    | spl13_24 ),
    inference(avatar_split_clause,[],[f820,f813,f809,f133])).

fof(f133,plain,
    ( spl13_3
  <=> k1_tarski(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f809,plain,
    ( spl13_23
  <=> r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f813,plain,
    ( spl13_24
  <=> r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f820,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | spl13_23
    | spl13_24 ),
    inference(subsumption_resolution,[],[f817,f815])).

fof(f815,plain,
    ( ~ r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | spl13_24 ),
    inference(avatar_component_clause,[],[f813])).

fof(f817,plain,
    ( r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | spl13_23 ),
    inference(resolution,[],[f811,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X1)
      | r2_hidden(sK11(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f811,plain,
    ( ~ r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | spl13_23 ),
    inference(avatar_component_clause,[],[f809])).

fof(f1473,plain,
    ( spl13_4
    | spl13_30
    | spl13_31 ),
    inference(avatar_contradiction_clause,[],[f1472])).

fof(f1472,plain,
    ( $false
    | spl13_4
    | spl13_30
    | spl13_31 ),
    inference(subsumption_resolution,[],[f1471,f139])).

fof(f1471,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | spl13_30
    | spl13_31 ),
    inference(subsumption_resolution,[],[f1468,f1464])).

fof(f1464,plain,
    ( ~ r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | spl13_31 ),
    inference(avatar_component_clause,[],[f1462])).

fof(f1462,plain,
    ( spl13_31
  <=> r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).

fof(f1468,plain,
    ( r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | spl13_30 ),
    inference(resolution,[],[f1460,f81])).

fof(f1460,plain,
    ( ~ r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2))
    | spl13_30 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f1458,plain,
    ( spl13_30
  <=> r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f1465,plain,
    ( ~ spl13_30
    | ~ spl13_31
    | spl13_4 ),
    inference(avatar_split_clause,[],[f1445,f137,f1462,f1458])).

fof(f1445,plain,
    ( ~ r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2))
    | spl13_4 ),
    inference(extensionality_resolution,[],[f82,f139])).

fof(f1450,plain,
    ( spl13_10
    | ~ spl13_13
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f1155,f621,f550,f314])).

fof(f550,plain,
    ( spl13_13
  <=> sK2 = k1_tarski(sK12(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f621,plain,
    ( spl13_15
  <=> k4_tarski(sK0,sK1) = sK12(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f1155,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl13_13
    | ~ spl13_15 ),
    inference(forward_demodulation,[],[f1151,f552])).

fof(f552,plain,
    ( sK2 = k1_tarski(sK12(sK2))
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f550])).

fof(f1151,plain,
    ( r2_hidden(sK0,k1_relat_1(k1_tarski(sK12(sK2))))
    | ~ spl13_15 ),
    inference(superposition,[],[f247,f623])).

fof(f623,plain,
    ( k4_tarski(sK0,sK1) = sK12(sK2)
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f621])).

fof(f247,plain,(
    ! [X2,X1] : r2_hidden(X1,k1_relat_1(k1_tarski(k4_tarski(X1,X2)))) ),
    inference(resolution,[],[f105,f112])).

fof(f105,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1387,plain,
    ( ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(avatar_contradiction_clause,[],[f1386])).

fof(f1386,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(subsumption_resolution,[],[f1385,f154])).

fof(f1385,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(forward_demodulation,[],[f1379,f151])).

fof(f1379,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(backward_demodulation,[],[f964,f1357])).

fof(f1357,plain,
    ( sK1 = sK11(k2_relat_1(sK2),k1_tarski(sK1))
    | ~ spl13_2
    | ~ spl13_23 ),
    inference(resolution,[],[f626,f810])).

fof(f810,plain,
    ( r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f809])).

fof(f626,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | sK1 = X1 )
    | ~ spl13_2 ),
    inference(resolution,[],[f324,f102])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f324,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 )
    | ~ spl13_2 ),
    inference(superposition,[],[f120,f130])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X1 = X3 ) ),
    inference(backward_demodulation,[],[f91,f99])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f964,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))))
    | spl13_24 ),
    inference(resolution,[],[f815,f70])).

fof(f1384,plain,
    ( ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(subsumption_resolution,[],[f1382,f154])).

fof(f1382,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(forward_demodulation,[],[f1378,f151])).

fof(f1378,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(backward_demodulation,[],[f963,f1357])).

fof(f963,plain,
    ( k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))) = k4_xboole_0(k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))),k1_tarski(sK1))
    | spl13_24 ),
    inference(resolution,[],[f815,f118])).

fof(f1381,plain,
    ( ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(avatar_contradiction_clause,[],[f1380])).

fof(f1380,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(subsumption_resolution,[],[f1375,f112])).

fof(f1375,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl13_2
    | ~ spl13_23
    | spl13_24 ),
    inference(backward_demodulation,[],[f815,f1357])).

fof(f1373,plain,
    ( ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(avatar_contradiction_clause,[],[f1372])).

fof(f1372,plain,
    ( $false
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f1371,f154])).

fof(f1371,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(forward_demodulation,[],[f1363,f151])).

fof(f1363,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f923,f1356])).

fof(f1356,plain,
    ( sK1 = sK11(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(resolution,[],[f626,f784])).

fof(f784,plain,
    ( r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f783])).

fof(f783,plain,
    ( spl13_22
  <=> r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f923,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))))
    | spl13_21 ),
    inference(resolution,[],[f781,f70])).

fof(f781,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | spl13_21 ),
    inference(avatar_component_clause,[],[f779])).

fof(f779,plain,
    ( spl13_21
  <=> r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f1370,plain,
    ( ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(avatar_contradiction_clause,[],[f1369])).

fof(f1369,plain,
    ( $false
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f1368,f154])).

fof(f1368,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(forward_demodulation,[],[f1362,f151])).

fof(f1362,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f922,f1356])).

fof(f922,plain,
    ( k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))) = k4_xboole_0(k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))),k1_tarski(sK1))
    | spl13_21 ),
    inference(resolution,[],[f781,f118])).

fof(f1367,plain,
    ( ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(avatar_contradiction_clause,[],[f1366])).

fof(f1366,plain,
    ( $false
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f1360,f112])).

fof(f1360,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl13_2
    | spl13_21
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f781,f1356])).

fof(f980,plain,
    ( ~ spl13_23
    | ~ spl13_24
    | spl13_3 ),
    inference(avatar_split_clause,[],[f899,f133,f813,f809])).

fof(f899,plain,
    ( ~ r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | ~ r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | spl13_3 ),
    inference(extensionality_resolution,[],[f82,f135])).

fof(f135,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f979,plain,
    ( ~ spl13_21
    | ~ spl13_22
    | spl13_3 ),
    inference(avatar_split_clause,[],[f898,f133,f783,f779])).

fof(f898,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | spl13_3 ),
    inference(extensionality_resolution,[],[f82,f135])).

fof(f974,plain,
    ( ~ spl13_29
    | ~ spl13_2
    | spl13_6
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f955,f550,f157,f128,f971])).

fof(f971,plain,
    ( spl13_29
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f157,plain,
    ( spl13_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f955,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK2)
    | ~ spl13_2
    | spl13_6
    | ~ spl13_13 ),
    inference(superposition,[],[f732,f552])).

fof(f732,plain,
    ( ! [X31] : k1_xboole_0 != k2_zfmisc_1(sK2,k1_tarski(X31))
    | ~ spl13_2
    | spl13_6 ),
    inference(superposition,[],[f154,f533])).

fof(f533,plain,
    ( ! [X0] : k2_zfmisc_1(sK2,k1_tarski(X0)) = k1_tarski(k4_tarski(sK12(sK2),X0))
    | ~ spl13_2
    | spl13_6 ),
    inference(backward_demodulation,[],[f251,f520])).

fof(f520,plain,
    ( k4_tarski(sK0,sK1) = sK12(sK2)
    | ~ spl13_2
    | spl13_6 ),
    inference(subsumption_resolution,[],[f519,f159])).

fof(f159,plain,
    ( k1_xboole_0 != sK2
    | spl13_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f519,plain,
    ( k4_tarski(sK0,sK1) = sK12(sK2)
    | k1_xboole_0 = sK2
    | ~ spl13_2 ),
    inference(resolution,[],[f167,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k4_tarski(sK0,sK1) = X0 )
    | ~ spl13_2 ),
    inference(superposition,[],[f110,f130])).

fof(f251,plain,
    ( ! [X0] : k1_tarski(k4_tarski(k4_tarski(sK0,sK1),X0)) = k2_zfmisc_1(sK2,k1_tarski(X0))
    | ~ spl13_2 ),
    inference(superposition,[],[f99,f130])).

fof(f969,plain,
    ( ~ spl13_28
    | spl13_26
    | spl13_27 ),
    inference(avatar_split_clause,[],[f887,f864,f860,f966])).

fof(f966,plain,
    ( spl13_28
  <=> r2_hidden(sK11(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f887,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))
    | spl13_26
    | spl13_27 ),
    inference(backward_demodulation,[],[f862,f874])).

fof(f874,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | spl13_26
    | spl13_27 ),
    inference(subsumption_resolution,[],[f871,f862])).

fof(f871,plain,
    ( r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | spl13_27 ),
    inference(resolution,[],[f866,f81])).

fof(f947,plain,
    ( ~ spl13_9
    | spl13_23
    | ~ spl13_24 ),
    inference(avatar_contradiction_clause,[],[f946])).

fof(f946,plain,
    ( $false
    | ~ spl13_9
    | spl13_23
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f945,f154])).

fof(f945,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl13_9
    | spl13_23
    | ~ spl13_24 ),
    inference(forward_demodulation,[],[f941,f355])).

fof(f355,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl13_9 ),
    inference(resolution,[],[f288,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f288,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl13_9
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f941,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k2_relat_1(sK2))
    | spl13_23
    | ~ spl13_24 ),
    inference(backward_demodulation,[],[f818,f935])).

fof(f935,plain,
    ( sK1 = sK11(k2_relat_1(sK2),k1_tarski(sK1))
    | ~ spl13_24 ),
    inference(resolution,[],[f814,f110])).

fof(f814,plain,
    ( r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f813])).

fof(f818,plain,
    ( k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))) = k4_xboole_0(k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))),k2_relat_1(sK2))
    | spl13_23 ),
    inference(resolution,[],[f811,f118])).

fof(f944,plain,
    ( ~ spl13_9
    | spl13_23
    | ~ spl13_24 ),
    inference(avatar_contradiction_clause,[],[f943])).

fof(f943,plain,
    ( $false
    | ~ spl13_9
    | spl13_23
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f940,f288])).

fof(f940,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl13_23
    | ~ spl13_24 ),
    inference(backward_demodulation,[],[f811,f935])).

fof(f917,plain,
    ( ~ spl13_9
    | ~ spl13_21
    | spl13_22 ),
    inference(avatar_contradiction_clause,[],[f916])).

fof(f916,plain,
    ( $false
    | ~ spl13_9
    | ~ spl13_21
    | spl13_22 ),
    inference(subsumption_resolution,[],[f915,f154])).

fof(f915,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl13_9
    | ~ spl13_21
    | spl13_22 ),
    inference(forward_demodulation,[],[f910,f355])).

fof(f910,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl13_21
    | spl13_22 ),
    inference(backward_demodulation,[],[f802,f905])).

fof(f905,plain,
    ( sK1 = sK11(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl13_21 ),
    inference(resolution,[],[f780,f110])).

fof(f780,plain,
    ( r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f779])).

fof(f802,plain,
    ( k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))) = k4_xboole_0(k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))),k2_relat_1(sK2))
    | spl13_22 ),
    inference(resolution,[],[f785,f118])).

fof(f785,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl13_22 ),
    inference(avatar_component_clause,[],[f783])).

fof(f914,plain,
    ( ~ spl13_9
    | ~ spl13_21
    | spl13_22 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl13_9
    | ~ spl13_21
    | spl13_22 ),
    inference(subsumption_resolution,[],[f909,f288])).

fof(f909,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl13_21
    | spl13_22 ),
    inference(backward_demodulation,[],[f785,f905])).

fof(f904,plain,
    ( spl13_4
    | spl13_26
    | spl13_27 ),
    inference(avatar_split_clause,[],[f874,f864,f860,f137])).

fof(f876,plain,
    ( spl13_4
    | spl13_26
    | spl13_27 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | spl13_4
    | spl13_26
    | spl13_27 ),
    inference(subsumption_resolution,[],[f874,f139])).

fof(f867,plain,
    ( ~ spl13_26
    | ~ spl13_27
    | spl13_4 ),
    inference(avatar_split_clause,[],[f358,f137,f864,f860])).

fof(f358,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | spl13_4 ),
    inference(extensionality_resolution,[],[f82,f139])).

fof(f849,plain,
    ( ~ spl13_25
    | spl13_22
    | spl13_23
    | spl13_24 ),
    inference(avatar_split_clause,[],[f833,f813,f809,f783,f846])).

fof(f846,plain,
    ( spl13_25
  <=> r2_hidden(sK11(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f833,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1))
    | spl13_22
    | spl13_23
    | spl13_24 ),
    inference(backward_demodulation,[],[f785,f820])).

fof(f844,plain,
    ( spl13_3
    | spl13_23
    | spl13_24 ),
    inference(avatar_split_clause,[],[f820,f813,f809,f133])).

fof(f822,plain,
    ( spl13_3
    | spl13_23
    | spl13_24 ),
    inference(avatar_contradiction_clause,[],[f821])).

fof(f821,plain,
    ( $false
    | spl13_3
    | spl13_23
    | spl13_24 ),
    inference(subsumption_resolution,[],[f820,f135])).

fof(f816,plain,
    ( ~ spl13_23
    | ~ spl13_24
    | spl13_3 ),
    inference(avatar_split_clause,[],[f357,f133,f813,f809])).

fof(f357,plain,
    ( ~ r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | ~ r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | spl13_3 ),
    inference(extensionality_resolution,[],[f82,f135])).

fof(f806,plain,
    ( spl13_3
    | spl13_21
    | spl13_22 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | spl13_3
    | spl13_21
    | spl13_22 ),
    inference(subsumption_resolution,[],[f804,f135])).

fof(f804,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | spl13_21
    | spl13_22 ),
    inference(subsumption_resolution,[],[f801,f781])).

fof(f801,plain,
    ( r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | spl13_22 ),
    inference(resolution,[],[f785,f81])).

fof(f786,plain,
    ( ~ spl13_21
    | ~ spl13_22
    | spl13_3 ),
    inference(avatar_split_clause,[],[f356,f133,f783,f779])).

fof(f356,plain,
    ( ~ r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | spl13_3 ),
    inference(extensionality_resolution,[],[f82,f135])).

fof(f716,plain,
    ( spl13_20
    | ~ spl13_2
    | spl13_6
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f661,f550,f157,f128,f713])).

fof(f713,plain,
    ( spl13_20
  <=> sK2 = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f661,plain,
    ( sK2 = k2_xboole_0(sK2,sK2)
    | ~ spl13_2
    | spl13_6
    | ~ spl13_13 ),
    inference(forward_demodulation,[],[f657,f552])).

fof(f657,plain,
    ( k1_tarski(sK12(sK2)) = k2_xboole_0(sK2,k1_tarski(sK12(sK2)))
    | ~ spl13_2
    | spl13_6 ),
    inference(superposition,[],[f531,f101])).

fof(f531,plain,
    ( ! [X0] : k2_xboole_0(sK2,k1_tarski(X0)) = k2_tarski(sK12(sK2),X0)
    | ~ spl13_2
    | spl13_6 ),
    inference(backward_demodulation,[],[f228,f520])).

fof(f228,plain,
    ( ! [X0] : k2_tarski(k4_tarski(sK0,sK1),X0) = k2_xboole_0(sK2,k1_tarski(X0))
    | ~ spl13_2 ),
    inference(superposition,[],[f100,f130])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f696,plain,
    ( ~ spl13_10
    | spl13_18 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl13_10
    | spl13_18 ),
    inference(subsumption_resolution,[],[f694,f316])).

fof(f694,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl13_18 ),
    inference(resolution,[],[f688,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f688,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_relat_1(sK2))
    | spl13_18 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl13_18
  <=> r1_tarski(k1_tarski(sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f693,plain,
    ( ~ spl13_18
    | ~ spl13_19
    | spl13_4 ),
    inference(avatar_split_clause,[],[f203,f137,f690,f686])).

fof(f690,plain,
    ( spl13_19
  <=> r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f203,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))
    | ~ r1_tarski(k1_tarski(sK0),k1_relat_1(sK2))
    | spl13_4 ),
    inference(extensionality_resolution,[],[f80,f139])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f682,plain,
    ( ~ spl13_9
    | spl13_16 ),
    inference(avatar_contradiction_clause,[],[f681])).

fof(f681,plain,
    ( $false
    | ~ spl13_9
    | spl13_16 ),
    inference(subsumption_resolution,[],[f680,f288])).

fof(f680,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl13_16 ),
    inference(resolution,[],[f674,f97])).

fof(f674,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k2_relat_1(sK2))
    | spl13_16 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl13_16
  <=> r1_tarski(k1_tarski(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f679,plain,
    ( ~ spl13_16
    | ~ spl13_17
    | spl13_3 ),
    inference(avatar_split_clause,[],[f201,f133,f676,f672])).

fof(f676,plain,
    ( spl13_17
  <=> r1_tarski(k2_relat_1(sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f201,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_tarski(sK1))
    | ~ r1_tarski(k1_tarski(sK1),k2_relat_1(sK2))
    | spl13_3 ),
    inference(extensionality_resolution,[],[f80,f135])).

fof(f624,plain,
    ( spl13_15
    | ~ spl13_2
    | spl13_6 ),
    inference(avatar_split_clause,[],[f520,f157,f128,f621])).

fof(f558,plain,
    ( spl13_14
    | ~ spl13_2
    | ~ spl13_5
    | spl13_6 ),
    inference(avatar_split_clause,[],[f522,f157,f143,f128,f555])).

fof(f555,plain,
    ( spl13_14
  <=> r2_hidden(sK12(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f143,plain,
    ( spl13_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f522,plain,
    ( r2_hidden(sK12(sK2),sK2)
    | ~ spl13_2
    | ~ spl13_5
    | spl13_6 ),
    inference(backward_demodulation,[],[f145,f520])).

fof(f145,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f553,plain,
    ( spl13_13
    | ~ spl13_2
    | spl13_6 ),
    inference(avatar_split_clause,[],[f521,f157,f128,f550])).

fof(f521,plain,
    ( sK2 = k1_tarski(sK12(sK2))
    | ~ spl13_2
    | spl13_6 ),
    inference(backward_demodulation,[],[f130,f520])).

fof(f452,plain,
    ( ~ spl13_12
    | spl13_6 ),
    inference(avatar_split_clause,[],[f380,f157,f449])).

fof(f449,plain,
    ( spl13_12
  <=> r2_hidden(sK11(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f380,plain,
    ( ~ r2_hidden(sK11(sK2,k1_xboole_0),k1_xboole_0)
    | spl13_6 ),
    inference(subsumption_resolution,[],[f365,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f106,f89])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f365,plain,
    ( ~ r2_hidden(sK11(sK2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK11(sK2,k1_xboole_0),sK2)
    | spl13_6 ),
    inference(extensionality_resolution,[],[f82,f159])).

fof(f433,plain,
    ( ~ spl13_11
    | spl13_6 ),
    inference(avatar_split_clause,[],[f379,f157,f430])).

fof(f430,plain,
    ( spl13_11
  <=> r2_hidden(sK11(k1_xboole_0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f379,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0,sK2),k1_xboole_0)
    | spl13_6 ),
    inference(subsumption_resolution,[],[f364,f172])).

fof(f364,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0,sK2),sK2)
    | ~ r2_hidden(sK11(k1_xboole_0,sK2),k1_xboole_0)
    | spl13_6 ),
    inference(extensionality_resolution,[],[f82,f159])).

fof(f317,plain,
    ( spl13_10
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f245,f143,f314])).

fof(f245,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl13_5 ),
    inference(resolution,[],[f105,f145])).

fof(f289,plain,
    ( spl13_9
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f239,f143,f286])).

fof(f239,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl13_5 ),
    inference(resolution,[],[f103,f145])).

fof(f103,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f227,plain,
    ( ~ spl13_7
    | ~ spl13_8
    | spl13_6 ),
    inference(avatar_split_clause,[],[f207,f157,f224,f220])).

fof(f220,plain,
    ( spl13_7
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f224,plain,
    ( spl13_8
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f207,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | spl13_6 ),
    inference(extensionality_resolution,[],[f80,f159])).

fof(f160,plain,
    ( ~ spl13_6
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f155,f128,f157])).

fof(f155,plain,
    ( k1_xboole_0 != sK2
    | ~ spl13_2 ),
    inference(superposition,[],[f154,f130])).

fof(f146,plain,
    ( spl13_5
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f141,f128,f143])).

fof(f141,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl13_2 ),
    inference(superposition,[],[f112,f130])).

fof(f140,plain,
    ( ~ spl13_3
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f49,f137,f133])).

fof(f49,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | k1_tarski(sK1) != k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f42])).

fof(f42,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f131,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f51,f128])).

fof(f51,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f126,plain,(
    spl13_1 ),
    inference(avatar_split_clause,[],[f50,f123])).

fof(f123,plain,
    ( spl13_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (11920)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (11928)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11911)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.21/0.53  % (11916)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 0.21/0.53  % (11913)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.21/0.53  % (11912)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.21/0.53  % (11932)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.21/0.54  % (11919)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (11907)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.21/0.54  % (11924)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 0.21/0.54  % (11927)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.21/0.54  % (11933)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 0.21/0.54  % (11930)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (11926)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 0.21/0.55  % (11905)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.21/0.55  % (11909)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.21/0.55  % (11921)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (11906)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.55  % (11931)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 0.21/0.55  % (11923)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (11934)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (11918)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.21/0.55  % (11929)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (11925)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.21/0.55  % (11929)Refutation not found, incomplete strategy% (11929)------------------------------
% 0.21/0.55  % (11929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11929)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11929)Memory used [KB]: 10746
% 0.21/0.55  % (11929)Time elapsed: 0.138 s
% 0.21/0.55  % (11929)------------------------------
% 0.21/0.55  % (11929)------------------------------
% 0.21/0.55  % (11922)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.21/0.56  % (11908)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.21/0.56  % (11908)Refutation not found, incomplete strategy% (11908)------------------------------
% 0.21/0.56  % (11908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11908)Memory used [KB]: 6140
% 0.21/0.56  % (11908)Time elapsed: 0.139 s
% 0.21/0.56  % (11908)------------------------------
% 0.21/0.56  % (11908)------------------------------
% 0.21/0.56  % (11915)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 0.21/0.56  % (11917)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.21/0.56  % (11914)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (11910)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 2.04/0.68  % (11961)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.04/0.70  % (11963)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 3.82/0.88  % (11928)Refutation found. Thanks to Tanya!
% 3.82/0.88  % SZS status Theorem for theBenchmark
% 3.82/0.88  % SZS output start Proof for theBenchmark
% 3.82/0.88  fof(f1570,plain,(
% 3.82/0.88    $false),
% 3.82/0.88    inference(avatar_sat_refutation,[],[f126,f131,f140,f146,f160,f227,f289,f317,f433,f452,f553,f558,f624,f679,f682,f693,f696,f716,f786,f806,f816,f822,f844,f849,f867,f876,f904,f914,f917,f944,f947,f969,f974,f979,f980,f1367,f1370,f1373,f1381,f1384,f1387,f1450,f1465,f1473,f1515,f1548,f1551,f1554,f1562,f1566])).
% 3.82/0.88  fof(f1566,plain,(
% 3.82/0.88    spl13_4 | ~spl13_10 | ~spl13_26),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1565])).
% 3.82/0.88  fof(f1565,plain,(
% 3.82/0.88    $false | (spl13_4 | ~spl13_10 | ~spl13_26)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1564,f316])).
% 3.82/0.88  fof(f316,plain,(
% 3.82/0.88    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl13_10),
% 3.82/0.88    inference(avatar_component_clause,[],[f314])).
% 3.82/0.88  fof(f314,plain,(
% 3.82/0.88    spl13_10 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 3.82/0.88  fof(f1564,plain,(
% 3.82/0.88    ~r2_hidden(sK0,k1_relat_1(sK2)) | (spl13_4 | ~spl13_26)),
% 3.82/0.88    inference(forward_demodulation,[],[f1563,f1555])).
% 3.82/0.88  fof(f1555,plain,(
% 3.82/0.88    sK0 = sK11(k1_tarski(sK0),k1_relat_1(sK2)) | ~spl13_26),
% 3.82/0.88    inference(resolution,[],[f861,f110])).
% 3.82/0.88  fof(f110,plain,(
% 3.82/0.88    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 3.82/0.88    inference(equality_resolution,[],[f75])).
% 3.82/0.88  fof(f75,plain,(
% 3.82/0.88    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f23])).
% 3.82/0.88  fof(f23,axiom,(
% 3.82/0.88    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 3.82/0.88  fof(f861,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) | ~spl13_26),
% 3.82/0.88    inference(avatar_component_clause,[],[f860])).
% 3.82/0.88  fof(f860,plain,(
% 3.82/0.88    spl13_26 <=> r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).
% 3.82/0.88  fof(f1563,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) | (spl13_4 | ~spl13_26)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1560,f112])).
% 3.82/0.88  fof(f112,plain,(
% 3.82/0.88    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 3.82/0.88    inference(equality_resolution,[],[f111])).
% 3.82/0.88  fof(f111,plain,(
% 3.82/0.88    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 3.82/0.88    inference(equality_resolution,[],[f74])).
% 3.82/0.88  fof(f74,plain,(
% 3.82/0.88    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f23])).
% 3.82/0.88  fof(f1560,plain,(
% 3.82/0.88    ~r2_hidden(sK0,k1_tarski(sK0)) | ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) | (spl13_4 | ~spl13_26)),
% 3.82/0.88    inference(backward_demodulation,[],[f1444,f1555])).
% 3.82/0.88  fof(f1444,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) | ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) | spl13_4),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f139])).
% 3.82/0.88  fof(f139,plain,(
% 3.82/0.88    k1_tarski(sK0) != k1_relat_1(sK2) | spl13_4),
% 3.82/0.88    inference(avatar_component_clause,[],[f137])).
% 3.82/0.88  fof(f137,plain,(
% 3.82/0.88    spl13_4 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 3.82/0.88  fof(f82,plain,(
% 3.82/0.88    ( ! [X0,X1] : (~r2_hidden(sK11(X0,X1),X1) | ~r2_hidden(sK11(X0,X1),X0) | X0 = X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f46])).
% 3.82/0.88  fof(f46,plain,(
% 3.82/0.88    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.82/0.88    inference(ennf_transformation,[],[f6])).
% 3.82/0.88  fof(f6,axiom,(
% 3.82/0.88    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 3.82/0.88  fof(f1562,plain,(
% 3.82/0.88    ~spl13_10 | ~spl13_26 | spl13_27),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1561])).
% 3.82/0.88  fof(f1561,plain,(
% 3.82/0.88    $false | (~spl13_10 | ~spl13_26 | spl13_27)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1559,f316])).
% 3.82/0.88  fof(f1559,plain,(
% 3.82/0.88    ~r2_hidden(sK0,k1_relat_1(sK2)) | (~spl13_26 | spl13_27)),
% 3.82/0.88    inference(backward_demodulation,[],[f866,f1555])).
% 3.82/0.88  fof(f866,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) | spl13_27),
% 3.82/0.88    inference(avatar_component_clause,[],[f864])).
% 3.82/0.88  fof(f864,plain,(
% 3.82/0.88    spl13_27 <=> r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).
% 3.82/0.88  fof(f1554,plain,(
% 3.82/0.88    ~spl13_2 | spl13_26 | ~spl13_27),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1553])).
% 3.82/0.88  fof(f1553,plain,(
% 3.82/0.88    $false | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1552,f154])).
% 3.82/0.88  fof(f154,plain,(
% 3.82/0.88    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 3.82/0.88    inference(backward_demodulation,[],[f109,f151])).
% 3.82/0.88  fof(f151,plain,(
% 3.82/0.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.82/0.88    inference(superposition,[],[f87,f89])).
% 3.82/0.88  fof(f89,plain,(
% 3.82/0.88    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.82/0.88    inference(cnf_transformation,[],[f10])).
% 3.82/0.88  fof(f10,axiom,(
% 3.82/0.88    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.82/0.88  fof(f87,plain,(
% 3.82/0.88    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.82/0.88    inference(cnf_transformation,[],[f19])).
% 3.82/0.88  fof(f19,axiom,(
% 3.82/0.88    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.82/0.88  fof(f109,plain,(
% 3.82/0.88    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 3.82/0.88    inference(equality_resolution,[],[f69])).
% 3.82/0.88  fof(f69,plain,(
% 3.82/0.88    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.82/0.88    inference(cnf_transformation,[],[f32])).
% 3.82/0.88  fof(f32,axiom,(
% 3.82/0.88    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 3.82/0.88  fof(f1552,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK0) | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(forward_demodulation,[],[f1546,f151])).
% 3.82/0.88  fof(f1546,plain,(
% 3.82/0.88    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(backward_demodulation,[],[f870,f1537])).
% 3.82/0.88  fof(f1537,plain,(
% 3.82/0.88    sK0 = sK11(k1_tarski(sK0),k1_relat_1(sK2)) | (~spl13_2 | ~spl13_27)),
% 3.82/0.88    inference(resolution,[],[f614,f865])).
% 3.82/0.88  fof(f865,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) | ~spl13_27),
% 3.82/0.88    inference(avatar_component_clause,[],[f864])).
% 3.82/0.88  fof(f614,plain,(
% 3.82/0.88    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl13_2),
% 3.82/0.88    inference(resolution,[],[f312,f104])).
% 3.82/0.88  fof(f104,plain,(
% 3.82/0.88    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 3.82/0.88    inference(equality_resolution,[],[f57])).
% 3.82/0.88  fof(f57,plain,(
% 3.82/0.88    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f40])).
% 3.82/0.88  fof(f40,axiom,(
% 3.82/0.88    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 3.82/0.88  fof(f312,plain,(
% 3.82/0.88    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f119,f130])).
% 3.82/0.88  fof(f130,plain,(
% 3.82/0.88    sK2 = k1_tarski(k4_tarski(sK0,sK1)) | ~spl13_2),
% 3.82/0.88    inference(avatar_component_clause,[],[f128])).
% 3.82/0.88  fof(f128,plain,(
% 3.82/0.88    spl13_2 <=> sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 3.82/0.88  fof(f119,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2) )),
% 3.82/0.88    inference(backward_demodulation,[],[f90,f99])).
% 3.82/0.88  fof(f99,plain,(
% 3.82/0.88    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 3.82/0.88    inference(cnf_transformation,[],[f34])).
% 3.82/0.88  fof(f34,axiom,(
% 3.82/0.88    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 3.82/0.88  fof(f90,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 3.82/0.88    inference(cnf_transformation,[],[f33])).
% 3.82/0.88  fof(f33,axiom,(
% 3.82/0.88    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 3.82/0.88  fof(f870,plain,(
% 3.82/0.88    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK11(k1_tarski(sK0),k1_relat_1(sK2)))) | spl13_26),
% 3.82/0.88    inference(resolution,[],[f862,f70])).
% 3.82/0.88  fof(f70,plain,(
% 3.82/0.88    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 3.82/0.88    inference(cnf_transformation,[],[f36])).
% 3.82/0.88  fof(f36,axiom,(
% 3.82/0.88    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 3.82/0.88  fof(f862,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) | spl13_26),
% 3.82/0.88    inference(avatar_component_clause,[],[f860])).
% 3.82/0.88  fof(f1551,plain,(
% 3.82/0.88    ~spl13_2 | spl13_26 | ~spl13_27),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1550])).
% 3.82/0.88  fof(f1550,plain,(
% 3.82/0.88    $false | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1549,f154])).
% 3.82/0.88  fof(f1549,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK0) | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(forward_demodulation,[],[f1545,f151])).
% 3.82/0.88  fof(f1545,plain,(
% 3.82/0.88    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(backward_demodulation,[],[f869,f1537])).
% 3.82/0.88  fof(f869,plain,(
% 3.82/0.88    k1_tarski(sK11(k1_tarski(sK0),k1_relat_1(sK2))) = k4_xboole_0(k1_tarski(sK11(k1_tarski(sK0),k1_relat_1(sK2))),k1_tarski(sK0)) | spl13_26),
% 3.82/0.88    inference(resolution,[],[f862,f118])).
% 3.82/0.88  fof(f118,plain,(
% 3.82/0.88    ( ! [X2,X1] : (r2_hidden(X1,X2) | k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)) )),
% 3.82/0.88    inference(forward_demodulation,[],[f117,f101])).
% 3.82/0.88  fof(f101,plain,(
% 3.82/0.88    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.82/0.88    inference(cnf_transformation,[],[f25])).
% 3.82/0.88  fof(f25,axiom,(
% 3.82/0.88    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.82/0.88  fof(f117,plain,(
% 3.82/0.88    ( ! [X2,X1] : (r2_hidden(X1,X2) | k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)) )),
% 3.82/0.88    inference(equality_resolution,[],[f94])).
% 3.82/0.88  fof(f94,plain,(
% 3.82/0.88    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | X0 != X1 | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.82/0.88    inference(cnf_transformation,[],[f28])).
% 3.82/0.88  fof(f28,axiom,(
% 3.82/0.88    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 3.82/0.88  fof(f1548,plain,(
% 3.82/0.88    ~spl13_2 | spl13_26 | ~spl13_27),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1547])).
% 3.82/0.88  fof(f1547,plain,(
% 3.82/0.88    $false | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1544,f112])).
% 3.82/0.88  fof(f1544,plain,(
% 3.82/0.88    ~r2_hidden(sK0,k1_tarski(sK0)) | (~spl13_2 | spl13_26 | ~spl13_27)),
% 3.82/0.88    inference(backward_demodulation,[],[f862,f1537])).
% 3.82/0.88  fof(f1515,plain,(
% 3.82/0.88    spl13_3 | spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_split_clause,[],[f820,f813,f809,f133])).
% 3.82/0.88  fof(f133,plain,(
% 3.82/0.88    spl13_3 <=> k1_tarski(sK1) = k2_relat_1(sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 3.82/0.88  fof(f809,plain,(
% 3.82/0.88    spl13_23 <=> r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).
% 3.82/0.88  fof(f813,plain,(
% 3.82/0.88    spl13_24 <=> r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).
% 3.82/0.88  fof(f820,plain,(
% 3.82/0.88    k1_tarski(sK1) = k2_relat_1(sK2) | (spl13_23 | spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f817,f815])).
% 3.82/0.88  fof(f815,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) | spl13_24),
% 3.82/0.88    inference(avatar_component_clause,[],[f813])).
% 3.82/0.88  fof(f817,plain,(
% 3.82/0.88    r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | spl13_23),
% 3.82/0.88    inference(resolution,[],[f811,f81])).
% 3.82/0.88  fof(f81,plain,(
% 3.82/0.88    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X1) | r2_hidden(sK11(X0,X1),X0) | X0 = X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f46])).
% 3.82/0.88  fof(f811,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) | spl13_23),
% 3.82/0.88    inference(avatar_component_clause,[],[f809])).
% 3.82/0.88  fof(f1473,plain,(
% 3.82/0.88    spl13_4 | spl13_30 | spl13_31),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1472])).
% 3.82/0.88  fof(f1472,plain,(
% 3.82/0.88    $false | (spl13_4 | spl13_30 | spl13_31)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1471,f139])).
% 3.82/0.88  fof(f1471,plain,(
% 3.82/0.88    k1_tarski(sK0) = k1_relat_1(sK2) | (spl13_30 | spl13_31)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1468,f1464])).
% 3.82/0.88  fof(f1464,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0)) | spl13_31),
% 3.82/0.88    inference(avatar_component_clause,[],[f1462])).
% 3.82/0.88  fof(f1462,plain,(
% 3.82/0.88    spl13_31 <=> r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).
% 3.82/0.88  fof(f1468,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2) | spl13_30),
% 3.82/0.88    inference(resolution,[],[f1460,f81])).
% 3.82/0.88  fof(f1460,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2)) | spl13_30),
% 3.82/0.88    inference(avatar_component_clause,[],[f1458])).
% 3.82/0.88  fof(f1458,plain,(
% 3.82/0.88    spl13_30 <=> r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).
% 3.82/0.88  fof(f1465,plain,(
% 3.82/0.88    ~spl13_30 | ~spl13_31 | spl13_4),
% 3.82/0.88    inference(avatar_split_clause,[],[f1445,f137,f1462,f1458])).
% 3.82/0.88  fof(f1445,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0)) | ~r2_hidden(sK11(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2)) | spl13_4),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f139])).
% 3.82/0.88  fof(f1450,plain,(
% 3.82/0.88    spl13_10 | ~spl13_13 | ~spl13_15),
% 3.82/0.88    inference(avatar_split_clause,[],[f1155,f621,f550,f314])).
% 3.82/0.88  fof(f550,plain,(
% 3.82/0.88    spl13_13 <=> sK2 = k1_tarski(sK12(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 3.82/0.88  fof(f621,plain,(
% 3.82/0.88    spl13_15 <=> k4_tarski(sK0,sK1) = sK12(sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 3.82/0.88  fof(f1155,plain,(
% 3.82/0.88    r2_hidden(sK0,k1_relat_1(sK2)) | (~spl13_13 | ~spl13_15)),
% 3.82/0.88    inference(forward_demodulation,[],[f1151,f552])).
% 3.82/0.88  fof(f552,plain,(
% 3.82/0.88    sK2 = k1_tarski(sK12(sK2)) | ~spl13_13),
% 3.82/0.88    inference(avatar_component_clause,[],[f550])).
% 3.82/0.88  fof(f1151,plain,(
% 3.82/0.88    r2_hidden(sK0,k1_relat_1(k1_tarski(sK12(sK2)))) | ~spl13_15),
% 3.82/0.88    inference(superposition,[],[f247,f623])).
% 3.82/0.88  fof(f623,plain,(
% 3.82/0.88    k4_tarski(sK0,sK1) = sK12(sK2) | ~spl13_15),
% 3.82/0.88    inference(avatar_component_clause,[],[f621])).
% 3.82/0.88  fof(f247,plain,(
% 3.82/0.88    ( ! [X2,X1] : (r2_hidden(X1,k1_relat_1(k1_tarski(k4_tarski(X1,X2))))) )),
% 3.82/0.88    inference(resolution,[],[f105,f112])).
% 3.82/0.88  fof(f105,plain,(
% 3.82/0.88    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 3.82/0.88    inference(equality_resolution,[],[f56])).
% 3.82/0.88  fof(f56,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f40])).
% 3.82/0.88  fof(f1387,plain,(
% 3.82/0.88    ~spl13_2 | ~spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1386])).
% 3.82/0.88  fof(f1386,plain,(
% 3.82/0.88    $false | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1385,f154])).
% 3.82/0.88  fof(f1385,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK1) | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(forward_demodulation,[],[f1379,f151])).
% 3.82/0.88  fof(f1379,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(backward_demodulation,[],[f964,f1357])).
% 3.82/0.88  fof(f1357,plain,(
% 3.82/0.88    sK1 = sK11(k2_relat_1(sK2),k1_tarski(sK1)) | (~spl13_2 | ~spl13_23)),
% 3.82/0.88    inference(resolution,[],[f626,f810])).
% 3.82/0.88  fof(f810,plain,(
% 3.82/0.88    r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) | ~spl13_23),
% 3.82/0.88    inference(avatar_component_clause,[],[f809])).
% 3.82/0.88  fof(f626,plain,(
% 3.82/0.88    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | sK1 = X1) ) | ~spl13_2),
% 3.82/0.88    inference(resolution,[],[f324,f102])).
% 3.82/0.88  fof(f102,plain,(
% 3.82/0.88    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 3.82/0.88    inference(equality_resolution,[],[f53])).
% 3.82/0.88  fof(f53,plain,(
% 3.82/0.88    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f41])).
% 3.82/0.88  fof(f41,axiom,(
% 3.82/0.88    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 3.82/0.88  fof(f324,plain,(
% 3.82/0.88    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) ) | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f120,f130])).
% 3.82/0.88  fof(f120,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X1 = X3) )),
% 3.82/0.88    inference(backward_demodulation,[],[f91,f99])).
% 3.82/0.88  fof(f91,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 3.82/0.88    inference(cnf_transformation,[],[f33])).
% 3.82/0.88  fof(f964,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1)))) | spl13_24),
% 3.82/0.88    inference(resolution,[],[f815,f70])).
% 3.82/0.88  fof(f1384,plain,(
% 3.82/0.88    ~spl13_2 | ~spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1383])).
% 3.82/0.88  fof(f1383,plain,(
% 3.82/0.88    $false | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1382,f154])).
% 3.82/0.88  fof(f1382,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK1) | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(forward_demodulation,[],[f1378,f151])).
% 3.82/0.88  fof(f1378,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(backward_demodulation,[],[f963,f1357])).
% 3.82/0.88  fof(f963,plain,(
% 3.82/0.88    k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))) = k4_xboole_0(k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))),k1_tarski(sK1)) | spl13_24),
% 3.82/0.88    inference(resolution,[],[f815,f118])).
% 3.82/0.88  fof(f1381,plain,(
% 3.82/0.88    ~spl13_2 | ~spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1380])).
% 3.82/0.88  fof(f1380,plain,(
% 3.82/0.88    $false | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1375,f112])).
% 3.82/0.88  fof(f1375,plain,(
% 3.82/0.88    ~r2_hidden(sK1,k1_tarski(sK1)) | (~spl13_2 | ~spl13_23 | spl13_24)),
% 3.82/0.88    inference(backward_demodulation,[],[f815,f1357])).
% 3.82/0.88  fof(f1373,plain,(
% 3.82/0.88    ~spl13_2 | spl13_21 | ~spl13_22),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1372])).
% 3.82/0.88  fof(f1372,plain,(
% 3.82/0.88    $false | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1371,f154])).
% 3.82/0.88  fof(f1371,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK1) | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(forward_demodulation,[],[f1363,f151])).
% 3.82/0.88  fof(f1363,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(backward_demodulation,[],[f923,f1356])).
% 3.82/0.88  fof(f1356,plain,(
% 3.82/0.88    sK1 = sK11(k1_tarski(sK1),k2_relat_1(sK2)) | (~spl13_2 | ~spl13_22)),
% 3.82/0.88    inference(resolution,[],[f626,f784])).
% 3.82/0.88  fof(f784,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl13_22),
% 3.82/0.88    inference(avatar_component_clause,[],[f783])).
% 3.82/0.88  fof(f783,plain,(
% 3.82/0.88    spl13_22 <=> r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).
% 3.82/0.88  fof(f923,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2)))) | spl13_21),
% 3.82/0.88    inference(resolution,[],[f781,f70])).
% 3.82/0.88  fof(f781,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) | spl13_21),
% 3.82/0.88    inference(avatar_component_clause,[],[f779])).
% 3.82/0.88  fof(f779,plain,(
% 3.82/0.88    spl13_21 <=> r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).
% 3.82/0.88  fof(f1370,plain,(
% 3.82/0.88    ~spl13_2 | spl13_21 | ~spl13_22),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1369])).
% 3.82/0.88  fof(f1369,plain,(
% 3.82/0.88    $false | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1368,f154])).
% 3.82/0.88  fof(f1368,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK1) | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(forward_demodulation,[],[f1362,f151])).
% 3.82/0.88  fof(f1362,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(backward_demodulation,[],[f922,f1356])).
% 3.82/0.88  fof(f922,plain,(
% 3.82/0.88    k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))) = k4_xboole_0(k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))),k1_tarski(sK1)) | spl13_21),
% 3.82/0.88    inference(resolution,[],[f781,f118])).
% 3.82/0.88  fof(f1367,plain,(
% 3.82/0.88    ~spl13_2 | spl13_21 | ~spl13_22),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f1366])).
% 3.82/0.88  fof(f1366,plain,(
% 3.82/0.88    $false | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f1360,f112])).
% 3.82/0.88  fof(f1360,plain,(
% 3.82/0.88    ~r2_hidden(sK1,k1_tarski(sK1)) | (~spl13_2 | spl13_21 | ~spl13_22)),
% 3.82/0.88    inference(backward_demodulation,[],[f781,f1356])).
% 3.82/0.88  fof(f980,plain,(
% 3.82/0.88    ~spl13_23 | ~spl13_24 | spl13_3),
% 3.82/0.88    inference(avatar_split_clause,[],[f899,f133,f813,f809])).
% 3.82/0.88  fof(f899,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) | ~r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) | spl13_3),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f135])).
% 3.82/0.88  fof(f135,plain,(
% 3.82/0.88    k1_tarski(sK1) != k2_relat_1(sK2) | spl13_3),
% 3.82/0.88    inference(avatar_component_clause,[],[f133])).
% 3.82/0.88  fof(f979,plain,(
% 3.82/0.88    ~spl13_21 | ~spl13_22 | spl13_3),
% 3.82/0.88    inference(avatar_split_clause,[],[f898,f133,f783,f779])).
% 3.82/0.88  fof(f898,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) | ~r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) | spl13_3),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f135])).
% 3.82/0.88  fof(f974,plain,(
% 3.82/0.88    ~spl13_29 | ~spl13_2 | spl13_6 | ~spl13_13),
% 3.82/0.88    inference(avatar_split_clause,[],[f955,f550,f157,f128,f971])).
% 3.82/0.88  fof(f971,plain,(
% 3.82/0.88    spl13_29 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).
% 3.82/0.88  fof(f157,plain,(
% 3.82/0.88    spl13_6 <=> k1_xboole_0 = sK2),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 3.82/0.88  fof(f955,plain,(
% 3.82/0.88    k1_xboole_0 != k2_zfmisc_1(sK2,sK2) | (~spl13_2 | spl13_6 | ~spl13_13)),
% 3.82/0.88    inference(superposition,[],[f732,f552])).
% 3.82/0.88  fof(f732,plain,(
% 3.82/0.88    ( ! [X31] : (k1_xboole_0 != k2_zfmisc_1(sK2,k1_tarski(X31))) ) | (~spl13_2 | spl13_6)),
% 3.82/0.88    inference(superposition,[],[f154,f533])).
% 3.82/0.88  fof(f533,plain,(
% 3.82/0.88    ( ! [X0] : (k2_zfmisc_1(sK2,k1_tarski(X0)) = k1_tarski(k4_tarski(sK12(sK2),X0))) ) | (~spl13_2 | spl13_6)),
% 3.82/0.88    inference(backward_demodulation,[],[f251,f520])).
% 3.82/0.88  fof(f520,plain,(
% 3.82/0.88    k4_tarski(sK0,sK1) = sK12(sK2) | (~spl13_2 | spl13_6)),
% 3.82/0.88    inference(subsumption_resolution,[],[f519,f159])).
% 3.82/0.88  fof(f159,plain,(
% 3.82/0.88    k1_xboole_0 != sK2 | spl13_6),
% 3.82/0.88    inference(avatar_component_clause,[],[f157])).
% 3.82/0.88  fof(f519,plain,(
% 3.82/0.88    k4_tarski(sK0,sK1) = sK12(sK2) | k1_xboole_0 = sK2 | ~spl13_2),
% 3.82/0.88    inference(resolution,[],[f167,f88])).
% 3.82/0.88  fof(f88,plain,(
% 3.82/0.88    ( ! [X0] : (r2_hidden(sK12(X0),X0) | k1_xboole_0 = X0) )),
% 3.82/0.88    inference(cnf_transformation,[],[f48])).
% 3.82/0.88  fof(f48,plain,(
% 3.82/0.88    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.82/0.88    inference(ennf_transformation,[],[f8])).
% 3.82/0.88  fof(f8,axiom,(
% 3.82/0.88    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.82/0.88  fof(f167,plain,(
% 3.82/0.88    ( ! [X0] : (~r2_hidden(X0,sK2) | k4_tarski(sK0,sK1) = X0) ) | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f110,f130])).
% 3.82/0.88  fof(f251,plain,(
% 3.82/0.88    ( ! [X0] : (k1_tarski(k4_tarski(k4_tarski(sK0,sK1),X0)) = k2_zfmisc_1(sK2,k1_tarski(X0))) ) | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f99,f130])).
% 3.82/0.88  fof(f969,plain,(
% 3.82/0.88    ~spl13_28 | spl13_26 | spl13_27),
% 3.82/0.88    inference(avatar_split_clause,[],[f887,f864,f860,f966])).
% 3.82/0.88  fof(f966,plain,(
% 3.82/0.88    spl13_28 <=> r2_hidden(sK11(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).
% 3.82/0.88  fof(f887,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0)) | (spl13_26 | spl13_27)),
% 3.82/0.88    inference(backward_demodulation,[],[f862,f874])).
% 3.82/0.88  fof(f874,plain,(
% 3.82/0.88    k1_tarski(sK0) = k1_relat_1(sK2) | (spl13_26 | spl13_27)),
% 3.82/0.88    inference(subsumption_resolution,[],[f871,f862])).
% 3.82/0.88  fof(f871,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2) | spl13_27),
% 3.82/0.88    inference(resolution,[],[f866,f81])).
% 3.82/0.88  fof(f947,plain,(
% 3.82/0.88    ~spl13_9 | spl13_23 | ~spl13_24),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f946])).
% 3.82/0.88  fof(f946,plain,(
% 3.82/0.88    $false | (~spl13_9 | spl13_23 | ~spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f945,f154])).
% 3.82/0.88  fof(f945,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK1) | (~spl13_9 | spl13_23 | ~spl13_24)),
% 3.82/0.88    inference(forward_demodulation,[],[f941,f355])).
% 3.82/0.88  fof(f355,plain,(
% 3.82/0.88    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_relat_1(sK2)) | ~spl13_9),
% 3.82/0.88    inference(resolution,[],[f288,f72])).
% 3.82/0.88  fof(f72,plain,(
% 3.82/0.88    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 3.82/0.88    inference(cnf_transformation,[],[f37])).
% 3.82/0.88  fof(f37,axiom,(
% 3.82/0.88    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 3.82/0.88  fof(f288,plain,(
% 3.82/0.88    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl13_9),
% 3.82/0.88    inference(avatar_component_clause,[],[f286])).
% 3.82/0.88  fof(f286,plain,(
% 3.82/0.88    spl13_9 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 3.82/0.88  fof(f941,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k2_relat_1(sK2)) | (spl13_23 | ~spl13_24)),
% 3.82/0.88    inference(backward_demodulation,[],[f818,f935])).
% 3.82/0.88  fof(f935,plain,(
% 3.82/0.88    sK1 = sK11(k2_relat_1(sK2),k1_tarski(sK1)) | ~spl13_24),
% 3.82/0.88    inference(resolution,[],[f814,f110])).
% 3.82/0.88  fof(f814,plain,(
% 3.82/0.88    r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) | ~spl13_24),
% 3.82/0.88    inference(avatar_component_clause,[],[f813])).
% 3.82/0.88  fof(f818,plain,(
% 3.82/0.88    k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))) = k4_xboole_0(k1_tarski(sK11(k2_relat_1(sK2),k1_tarski(sK1))),k2_relat_1(sK2)) | spl13_23),
% 3.82/0.88    inference(resolution,[],[f811,f118])).
% 3.82/0.88  fof(f944,plain,(
% 3.82/0.88    ~spl13_9 | spl13_23 | ~spl13_24),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f943])).
% 3.82/0.88  fof(f943,plain,(
% 3.82/0.88    $false | (~spl13_9 | spl13_23 | ~spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f940,f288])).
% 3.82/0.88  fof(f940,plain,(
% 3.82/0.88    ~r2_hidden(sK1,k2_relat_1(sK2)) | (spl13_23 | ~spl13_24)),
% 3.82/0.88    inference(backward_demodulation,[],[f811,f935])).
% 3.82/0.88  fof(f917,plain,(
% 3.82/0.88    ~spl13_9 | ~spl13_21 | spl13_22),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f916])).
% 3.82/0.88  fof(f916,plain,(
% 3.82/0.88    $false | (~spl13_9 | ~spl13_21 | spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f915,f154])).
% 3.82/0.88  fof(f915,plain,(
% 3.82/0.88    k1_xboole_0 = k1_tarski(sK1) | (~spl13_9 | ~spl13_21 | spl13_22)),
% 3.82/0.88    inference(forward_demodulation,[],[f910,f355])).
% 3.82/0.88  fof(f910,plain,(
% 3.82/0.88    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k2_relat_1(sK2)) | (~spl13_21 | spl13_22)),
% 3.82/0.88    inference(backward_demodulation,[],[f802,f905])).
% 3.82/0.88  fof(f905,plain,(
% 3.82/0.88    sK1 = sK11(k1_tarski(sK1),k2_relat_1(sK2)) | ~spl13_21),
% 3.82/0.88    inference(resolution,[],[f780,f110])).
% 3.82/0.88  fof(f780,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) | ~spl13_21),
% 3.82/0.88    inference(avatar_component_clause,[],[f779])).
% 3.82/0.88  fof(f802,plain,(
% 3.82/0.88    k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))) = k4_xboole_0(k1_tarski(sK11(k1_tarski(sK1),k2_relat_1(sK2))),k2_relat_1(sK2)) | spl13_22),
% 3.82/0.88    inference(resolution,[],[f785,f118])).
% 3.82/0.88  fof(f785,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) | spl13_22),
% 3.82/0.88    inference(avatar_component_clause,[],[f783])).
% 3.82/0.88  fof(f914,plain,(
% 3.82/0.88    ~spl13_9 | ~spl13_21 | spl13_22),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f913])).
% 3.82/0.88  fof(f913,plain,(
% 3.82/0.88    $false | (~spl13_9 | ~spl13_21 | spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f909,f288])).
% 3.82/0.88  fof(f909,plain,(
% 3.82/0.88    ~r2_hidden(sK1,k2_relat_1(sK2)) | (~spl13_21 | spl13_22)),
% 3.82/0.88    inference(backward_demodulation,[],[f785,f905])).
% 3.82/0.88  fof(f904,plain,(
% 3.82/0.88    spl13_4 | spl13_26 | spl13_27),
% 3.82/0.88    inference(avatar_split_clause,[],[f874,f864,f860,f137])).
% 3.82/0.88  fof(f876,plain,(
% 3.82/0.88    spl13_4 | spl13_26 | spl13_27),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f875])).
% 3.82/0.88  fof(f875,plain,(
% 3.82/0.88    $false | (spl13_4 | spl13_26 | spl13_27)),
% 3.82/0.88    inference(subsumption_resolution,[],[f874,f139])).
% 3.82/0.88  fof(f867,plain,(
% 3.82/0.88    ~spl13_26 | ~spl13_27 | spl13_4),
% 3.82/0.88    inference(avatar_split_clause,[],[f358,f137,f864,f860])).
% 3.82/0.88  fof(f358,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) | ~r2_hidden(sK11(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) | spl13_4),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f139])).
% 3.82/0.88  fof(f849,plain,(
% 3.82/0.88    ~spl13_25 | spl13_22 | spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_split_clause,[],[f833,f813,f809,f783,f846])).
% 3.82/0.88  fof(f846,plain,(
% 3.82/0.88    spl13_25 <=> r2_hidden(sK11(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).
% 3.82/0.88  fof(f833,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1)) | (spl13_22 | spl13_23 | spl13_24)),
% 3.82/0.88    inference(backward_demodulation,[],[f785,f820])).
% 3.82/0.88  fof(f844,plain,(
% 3.82/0.88    spl13_3 | spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_split_clause,[],[f820,f813,f809,f133])).
% 3.82/0.88  fof(f822,plain,(
% 3.82/0.88    spl13_3 | spl13_23 | spl13_24),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f821])).
% 3.82/0.88  fof(f821,plain,(
% 3.82/0.88    $false | (spl13_3 | spl13_23 | spl13_24)),
% 3.82/0.88    inference(subsumption_resolution,[],[f820,f135])).
% 3.82/0.88  fof(f816,plain,(
% 3.82/0.88    ~spl13_23 | ~spl13_24 | spl13_3),
% 3.82/0.88    inference(avatar_split_clause,[],[f357,f133,f813,f809])).
% 3.82/0.88  fof(f357,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) | ~r2_hidden(sK11(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) | spl13_3),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f135])).
% 3.82/0.88  fof(f806,plain,(
% 3.82/0.88    spl13_3 | spl13_21 | spl13_22),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f805])).
% 3.82/0.88  fof(f805,plain,(
% 3.82/0.88    $false | (spl13_3 | spl13_21 | spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f804,f135])).
% 3.82/0.88  fof(f804,plain,(
% 3.82/0.88    k1_tarski(sK1) = k2_relat_1(sK2) | (spl13_21 | spl13_22)),
% 3.82/0.88    inference(subsumption_resolution,[],[f801,f781])).
% 3.82/0.88  fof(f801,plain,(
% 3.82/0.88    r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | spl13_22),
% 3.82/0.88    inference(resolution,[],[f785,f81])).
% 3.82/0.88  fof(f786,plain,(
% 3.82/0.88    ~spl13_21 | ~spl13_22 | spl13_3),
% 3.82/0.88    inference(avatar_split_clause,[],[f356,f133,f783,f779])).
% 3.82/0.88  fof(f356,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) | ~r2_hidden(sK11(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) | spl13_3),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f135])).
% 3.82/0.88  fof(f716,plain,(
% 3.82/0.88    spl13_20 | ~spl13_2 | spl13_6 | ~spl13_13),
% 3.82/0.88    inference(avatar_split_clause,[],[f661,f550,f157,f128,f713])).
% 3.82/0.88  fof(f713,plain,(
% 3.82/0.88    spl13_20 <=> sK2 = k2_xboole_0(sK2,sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 3.82/0.88  fof(f661,plain,(
% 3.82/0.88    sK2 = k2_xboole_0(sK2,sK2) | (~spl13_2 | spl13_6 | ~spl13_13)),
% 3.82/0.88    inference(forward_demodulation,[],[f657,f552])).
% 3.82/0.88  fof(f657,plain,(
% 3.82/0.88    k1_tarski(sK12(sK2)) = k2_xboole_0(sK2,k1_tarski(sK12(sK2))) | (~spl13_2 | spl13_6)),
% 3.82/0.88    inference(superposition,[],[f531,f101])).
% 3.82/0.88  fof(f531,plain,(
% 3.82/0.88    ( ! [X0] : (k2_xboole_0(sK2,k1_tarski(X0)) = k2_tarski(sK12(sK2),X0)) ) | (~spl13_2 | spl13_6)),
% 3.82/0.88    inference(backward_demodulation,[],[f228,f520])).
% 3.82/0.88  fof(f228,plain,(
% 3.82/0.88    ( ! [X0] : (k2_tarski(k4_tarski(sK0,sK1),X0) = k2_xboole_0(sK2,k1_tarski(X0))) ) | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f100,f130])).
% 3.82/0.88  fof(f100,plain,(
% 3.82/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.82/0.88    inference(cnf_transformation,[],[f24])).
% 3.82/0.88  fof(f24,axiom,(
% 3.82/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 3.82/0.88  fof(f696,plain,(
% 3.82/0.88    ~spl13_10 | spl13_18),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f695])).
% 3.82/0.88  fof(f695,plain,(
% 3.82/0.88    $false | (~spl13_10 | spl13_18)),
% 3.82/0.88    inference(subsumption_resolution,[],[f694,f316])).
% 3.82/0.88  fof(f694,plain,(
% 3.82/0.88    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl13_18),
% 3.82/0.88    inference(resolution,[],[f688,f97])).
% 3.82/0.88  fof(f97,plain,(
% 3.82/0.88    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.82/0.88    inference(cnf_transformation,[],[f35])).
% 3.82/0.88  fof(f35,axiom,(
% 3.82/0.88    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 3.82/0.88  fof(f688,plain,(
% 3.82/0.88    ~r1_tarski(k1_tarski(sK0),k1_relat_1(sK2)) | spl13_18),
% 3.82/0.88    inference(avatar_component_clause,[],[f686])).
% 3.82/0.88  fof(f686,plain,(
% 3.82/0.88    spl13_18 <=> r1_tarski(k1_tarski(sK0),k1_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 3.82/0.88  fof(f693,plain,(
% 3.82/0.88    ~spl13_18 | ~spl13_19 | spl13_4),
% 3.82/0.88    inference(avatar_split_clause,[],[f203,f137,f690,f686])).
% 3.82/0.88  fof(f690,plain,(
% 3.82/0.88    spl13_19 <=> r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 3.82/0.88  fof(f203,plain,(
% 3.82/0.88    ~r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) | ~r1_tarski(k1_tarski(sK0),k1_relat_1(sK2)) | spl13_4),
% 3.82/0.88    inference(extensionality_resolution,[],[f80,f139])).
% 3.82/0.88  fof(f80,plain,(
% 3.82/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f9])).
% 3.82/0.88  fof(f9,axiom,(
% 3.82/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.82/0.88  fof(f682,plain,(
% 3.82/0.88    ~spl13_9 | spl13_16),
% 3.82/0.88    inference(avatar_contradiction_clause,[],[f681])).
% 3.82/0.88  fof(f681,plain,(
% 3.82/0.88    $false | (~spl13_9 | spl13_16)),
% 3.82/0.88    inference(subsumption_resolution,[],[f680,f288])).
% 3.82/0.88  fof(f680,plain,(
% 3.82/0.88    ~r2_hidden(sK1,k2_relat_1(sK2)) | spl13_16),
% 3.82/0.88    inference(resolution,[],[f674,f97])).
% 3.82/0.88  fof(f674,plain,(
% 3.82/0.88    ~r1_tarski(k1_tarski(sK1),k2_relat_1(sK2)) | spl13_16),
% 3.82/0.88    inference(avatar_component_clause,[],[f672])).
% 3.82/0.88  fof(f672,plain,(
% 3.82/0.88    spl13_16 <=> r1_tarski(k1_tarski(sK1),k2_relat_1(sK2))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 3.82/0.88  fof(f679,plain,(
% 3.82/0.88    ~spl13_16 | ~spl13_17 | spl13_3),
% 3.82/0.88    inference(avatar_split_clause,[],[f201,f133,f676,f672])).
% 3.82/0.88  fof(f676,plain,(
% 3.82/0.88    spl13_17 <=> r1_tarski(k2_relat_1(sK2),k1_tarski(sK1))),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 3.82/0.88  fof(f201,plain,(
% 3.82/0.88    ~r1_tarski(k2_relat_1(sK2),k1_tarski(sK1)) | ~r1_tarski(k1_tarski(sK1),k2_relat_1(sK2)) | spl13_3),
% 3.82/0.88    inference(extensionality_resolution,[],[f80,f135])).
% 3.82/0.88  fof(f624,plain,(
% 3.82/0.88    spl13_15 | ~spl13_2 | spl13_6),
% 3.82/0.88    inference(avatar_split_clause,[],[f520,f157,f128,f621])).
% 3.82/0.88  fof(f558,plain,(
% 3.82/0.88    spl13_14 | ~spl13_2 | ~spl13_5 | spl13_6),
% 3.82/0.88    inference(avatar_split_clause,[],[f522,f157,f143,f128,f555])).
% 3.82/0.88  fof(f555,plain,(
% 3.82/0.88    spl13_14 <=> r2_hidden(sK12(sK2),sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 3.82/0.88  fof(f143,plain,(
% 3.82/0.88    spl13_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 3.82/0.88  fof(f522,plain,(
% 3.82/0.88    r2_hidden(sK12(sK2),sK2) | (~spl13_2 | ~spl13_5 | spl13_6)),
% 3.82/0.88    inference(backward_demodulation,[],[f145,f520])).
% 3.82/0.88  fof(f145,plain,(
% 3.82/0.88    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl13_5),
% 3.82/0.88    inference(avatar_component_clause,[],[f143])).
% 3.82/0.88  fof(f553,plain,(
% 3.82/0.88    spl13_13 | ~spl13_2 | spl13_6),
% 3.82/0.88    inference(avatar_split_clause,[],[f521,f157,f128,f550])).
% 3.82/0.88  fof(f521,plain,(
% 3.82/0.88    sK2 = k1_tarski(sK12(sK2)) | (~spl13_2 | spl13_6)),
% 3.82/0.88    inference(backward_demodulation,[],[f130,f520])).
% 3.82/0.88  fof(f452,plain,(
% 3.82/0.88    ~spl13_12 | spl13_6),
% 3.82/0.88    inference(avatar_split_clause,[],[f380,f157,f449])).
% 3.82/0.88  fof(f449,plain,(
% 3.82/0.88    spl13_12 <=> r2_hidden(sK11(sK2,k1_xboole_0),k1_xboole_0)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 3.82/0.88  fof(f380,plain,(
% 3.82/0.88    ~r2_hidden(sK11(sK2,k1_xboole_0),k1_xboole_0) | spl13_6),
% 3.82/0.88    inference(subsumption_resolution,[],[f365,f172])).
% 3.82/0.88  fof(f172,plain,(
% 3.82/0.88    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 3.82/0.88    inference(superposition,[],[f106,f89])).
% 3.82/0.88  fof(f106,plain,(
% 3.82/0.88    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 3.82/0.88    inference(equality_resolution,[],[f65])).
% 3.82/0.88  fof(f65,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.82/0.88    inference(cnf_transformation,[],[f5])).
% 3.82/0.88  fof(f5,axiom,(
% 3.82/0.88    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.82/0.88  fof(f365,plain,(
% 3.82/0.88    ~r2_hidden(sK11(sK2,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK11(sK2,k1_xboole_0),sK2) | spl13_6),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f159])).
% 3.82/0.88  fof(f433,plain,(
% 3.82/0.88    ~spl13_11 | spl13_6),
% 3.82/0.88    inference(avatar_split_clause,[],[f379,f157,f430])).
% 3.82/0.88  fof(f430,plain,(
% 3.82/0.88    spl13_11 <=> r2_hidden(sK11(k1_xboole_0,sK2),k1_xboole_0)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 3.82/0.88  fof(f379,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_xboole_0,sK2),k1_xboole_0) | spl13_6),
% 3.82/0.88    inference(subsumption_resolution,[],[f364,f172])).
% 3.82/0.88  fof(f364,plain,(
% 3.82/0.88    ~r2_hidden(sK11(k1_xboole_0,sK2),sK2) | ~r2_hidden(sK11(k1_xboole_0,sK2),k1_xboole_0) | spl13_6),
% 3.82/0.88    inference(extensionality_resolution,[],[f82,f159])).
% 3.82/0.88  fof(f317,plain,(
% 3.82/0.88    spl13_10 | ~spl13_5),
% 3.82/0.88    inference(avatar_split_clause,[],[f245,f143,f314])).
% 3.82/0.88  fof(f245,plain,(
% 3.82/0.88    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl13_5),
% 3.82/0.88    inference(resolution,[],[f105,f145])).
% 3.82/0.88  fof(f289,plain,(
% 3.82/0.88    spl13_9 | ~spl13_5),
% 3.82/0.88    inference(avatar_split_clause,[],[f239,f143,f286])).
% 3.82/0.88  fof(f239,plain,(
% 3.82/0.88    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl13_5),
% 3.82/0.88    inference(resolution,[],[f103,f145])).
% 3.82/0.88  fof(f103,plain,(
% 3.82/0.88    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 3.82/0.88    inference(equality_resolution,[],[f52])).
% 3.82/0.88  fof(f52,plain,(
% 3.82/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 3.82/0.88    inference(cnf_transformation,[],[f41])).
% 3.82/0.88  fof(f227,plain,(
% 3.82/0.88    ~spl13_7 | ~spl13_8 | spl13_6),
% 3.82/0.88    inference(avatar_split_clause,[],[f207,f157,f224,f220])).
% 3.82/0.88  fof(f220,plain,(
% 3.82/0.88    spl13_7 <=> r1_tarski(k1_xboole_0,sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 3.82/0.88  fof(f224,plain,(
% 3.82/0.88    spl13_8 <=> r1_tarski(sK2,k1_xboole_0)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 3.82/0.88  fof(f207,plain,(
% 3.82/0.88    ~r1_tarski(sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK2) | spl13_6),
% 3.82/0.88    inference(extensionality_resolution,[],[f80,f159])).
% 3.82/0.88  fof(f160,plain,(
% 3.82/0.88    ~spl13_6 | ~spl13_2),
% 3.82/0.88    inference(avatar_split_clause,[],[f155,f128,f157])).
% 3.82/0.88  fof(f155,plain,(
% 3.82/0.88    k1_xboole_0 != sK2 | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f154,f130])).
% 3.82/0.88  fof(f146,plain,(
% 3.82/0.88    spl13_5 | ~spl13_2),
% 3.82/0.88    inference(avatar_split_clause,[],[f141,f128,f143])).
% 3.82/0.88  fof(f141,plain,(
% 3.82/0.88    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl13_2),
% 3.82/0.88    inference(superposition,[],[f112,f130])).
% 3.82/0.88  fof(f140,plain,(
% 3.82/0.88    ~spl13_3 | ~spl13_4),
% 3.82/0.88    inference(avatar_split_clause,[],[f49,f137,f133])).
% 3.82/0.88  fof(f49,plain,(
% 3.82/0.88    k1_tarski(sK0) != k1_relat_1(sK2) | k1_tarski(sK1) != k2_relat_1(sK2)),
% 3.82/0.88    inference(cnf_transformation,[],[f45])).
% 3.82/0.88  fof(f45,plain,(
% 3.82/0.88    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 3.82/0.88    inference(flattening,[],[f44])).
% 3.82/0.88  fof(f44,plain,(
% 3.82/0.88    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 3.82/0.88    inference(ennf_transformation,[],[f43])).
% 3.82/0.88  fof(f43,negated_conjecture,(
% 3.82/0.88    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 3.82/0.88    inference(negated_conjecture,[],[f42])).
% 3.82/0.88  fof(f42,conjecture,(
% 3.82/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 3.82/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 3.82/0.88  fof(f131,plain,(
% 3.82/0.88    spl13_2),
% 3.82/0.88    inference(avatar_split_clause,[],[f51,f128])).
% 3.82/0.88  fof(f51,plain,(
% 3.82/0.88    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 3.82/0.88    inference(cnf_transformation,[],[f45])).
% 3.82/0.88  fof(f126,plain,(
% 3.82/0.88    spl13_1),
% 3.82/0.88    inference(avatar_split_clause,[],[f50,f123])).
% 3.82/0.88  fof(f123,plain,(
% 3.82/0.88    spl13_1 <=> v1_relat_1(sK2)),
% 3.82/0.88    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 3.82/0.88  fof(f50,plain,(
% 3.82/0.88    v1_relat_1(sK2)),
% 3.82/0.88    inference(cnf_transformation,[],[f45])).
% 3.82/0.88  % SZS output end Proof for theBenchmark
% 3.82/0.88  % (11928)------------------------------
% 3.82/0.88  % (11928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.88  % (11928)Termination reason: Refutation
% 3.82/0.88  
% 3.82/0.88  % (11928)Memory used [KB]: 7675
% 3.82/0.88  % (11928)Time elapsed: 0.454 s
% 3.82/0.88  % (11928)------------------------------
% 3.82/0.88  % (11928)------------------------------
% 3.82/0.89  % (11904)Success in time 0.518 s
%------------------------------------------------------------------------------
