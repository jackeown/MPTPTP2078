%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t117_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:21 EDT 2019

% Result     : Theorem 18.92s
% Output     : Refutation 18.92s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 150 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  231 ( 378 expanded)
%              Number of equality atoms :   20 (  51 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6050,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f294,f321,f885,f1317,f1482,f1484,f1486,f6047,f6049])).

fof(f6049,plain,
    ( spl8_15
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f6048])).

fof(f6048,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1475,f1507])).

fof(f1507,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl8_15 ),
    inference(resolution,[],[f284,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t117_xboole_1.p',d3_xboole_0)).

fof(f284,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl8_15
  <=> ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f1475,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f1474,plain,
    ( spl8_24
  <=> r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f6047,plain,
    ( spl8_15
    | ~ spl8_16
    | spl8_19
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f6046])).

fof(f6046,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f6045,f320])).

fof(f320,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl8_19
  <=> ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f6045,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f6033,f1547])).

fof(f1547,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK1)
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(resolution,[],[f1506,f891])).

fof(f891,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK0,X1))
        | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),X1) )
    | ~ spl8_16 ),
    inference(resolution,[],[f293,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t117_xboole_1.p',d5_xboole_0)).

fof(f293,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl8_16
  <=> r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f1506,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK0,sK1))
    | ~ spl8_15 ),
    inference(resolution,[],[f284,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f6033,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK1)
    | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | ~ spl8_16
    | ~ spl8_25 ),
    inference(resolution,[],[f1582,f88])).

fof(f1582,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK1,sK2))
    | ~ spl8_16
    | ~ spl8_25 ),
    inference(resolution,[],[f1472,f894])).

fof(f894,plain,
    ( ! [X4] :
        ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,X4))
        | ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),X4) )
    | ~ spl8_16 ),
    inference(resolution,[],[f293,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t117_xboole_1.p',d4_xboole_0)).

fof(f1472,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f1471,plain,
    ( spl8_25
  <=> ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f1486,plain,
    ( ~ spl8_18
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f1485])).

fof(f1485,plain,
    ( $false
    | ~ spl8_18
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f1481,f923])).

fof(f923,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(X2,sK1))
    | ~ spl8_18 ),
    inference(resolution,[],[f898,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f898,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK1)
    | ~ spl8_18 ),
    inference(resolution,[],[f317,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t117_xboole_1.p',d3_tarski)).

fof(f42,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t117_xboole_1.p',t117_xboole_1)).

fof(f317,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl8_18
  <=> r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1481,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK0,sK1))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1480,plain,
    ( spl8_26
  <=> r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1484,plain,
    ( ~ spl8_18
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f1483])).

fof(f1483,plain,
    ( $false
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1475,f984])).

fof(f984,plain,
    ( ! [X8,X9] : ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(X8,k4_xboole_0(X9,sK2)))
    | ~ spl8_18 ),
    inference(resolution,[],[f905,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f905,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(X2,sK2))
    | ~ spl8_18 ),
    inference(resolution,[],[f317,f89])).

fof(f1482,plain,
    ( spl8_24
    | spl8_26
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f295,f286,f1480,f1474])).

fof(f286,plain,
    ( spl8_14
  <=> r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f295,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl8_14 ),
    inference(resolution,[],[f287,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f287,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f286])).

fof(f1317,plain,
    ( spl8_18
    | ~ spl8_17
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f307,f286,f289,f316])).

fof(f289,plain,
    ( spl8_17
  <=> ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f307,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0)
    | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f306,f98])).

fof(f98,plain,(
    ~ sQ7_eqProxy(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(equality_proxy_replacement,[],[f43,f97])).

fof(f97,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f43,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f306,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0)
    | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | sQ7_eqProxy(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | ~ spl8_14 ),
    inference(resolution,[],[f287,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f68,f97])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f885,plain,
    ( ~ spl8_14
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f876])).

fof(f876,plain,
    ( $false
    | ~ spl8_14
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f326,f287,f328,f96])).

fof(f328,plain,
    ( ! [X4] : ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,X4))
    | ~ spl8_17 ),
    inference(resolution,[],[f290,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f290,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f289])).

fof(f326,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k4_xboole_0(sK0,X2))
    | ~ spl8_17 ),
    inference(resolution,[],[f290,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f321,plain,
    ( spl8_14
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f151,f319,f286])).

fof(f151,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK2)
    | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f98,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f70,f97])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f294,plain,
    ( spl8_14
    | spl8_16 ),
    inference(avatar_split_clause,[],[f150,f292,f286])).

fof(f150,plain,
    ( r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0)
    | r2_hidden(sK4(sK0,sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f98,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f69,f97])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
