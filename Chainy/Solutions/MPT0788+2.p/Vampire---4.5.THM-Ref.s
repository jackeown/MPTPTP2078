%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0788+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 184 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  397 (1049 expanded)
%              Number of equality atoms :   61 ( 179 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1336,f1344,f1348,f1352,f1356,f1360,f1364,f1718,f1726,f1728,f1764,f1771])).

fof(f1771,plain,
    ( spl14_2
    | spl14_4
    | ~ spl14_8
    | ~ spl14_30 ),
    inference(avatar_contradiction_clause,[],[f1765])).

fof(f1765,plain,
    ( $false
    | spl14_2
    | spl14_4
    | ~ spl14_8
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f1363,f1343,f1335,f1763,f1323])).

fof(f1323,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1273])).

fof(f1273,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f1229,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                | sK3(X0,X1,X2) = X1
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                  & sK3(X0,X1,X2) != X1 )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1227,f1228])).

fof(f1228,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
          | sK3(X0,X1,X2) = X1
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
            & sK3(X0,X1,X2) != X1 )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1227,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1226])).

fof(f1226,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1225])).

fof(f1225,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1187])).

fof(f1187,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1130])).

fof(f1130,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f1763,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f1716])).

fof(f1716,plain,
    ( spl14_30
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f1335,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | spl14_2 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1334,plain,
    ( spl14_2
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1343,plain,
    ( sK0 != sK1
    | spl14_4 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1342,plain,
    ( spl14_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f1363,plain,
    ( v1_relat_1(sK2)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f1362,plain,
    ( spl14_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f1764,plain,
    ( spl14_30
    | ~ spl14_1
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f1762,f1362,f1358,f1354,f1350,f1331,f1716])).

fof(f1331,plain,
    ( spl14_1
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f1350,plain,
    ( spl14_5
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f1354,plain,
    ( spl14_6
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f1358,plain,
    ( spl14_7
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f1762,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_1
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f1761,f1363])).

fof(f1761,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_1
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f1760,f1359])).

fof(f1359,plain,
    ( v2_wellord1(sK2)
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f1358])).

fof(f1760,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_1
    | ~ spl14_5
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f1759,f1355])).

fof(f1355,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f1354])).

fof(f1759,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_1
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1745,f1351])).

fof(f1351,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1745,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_1 ),
    inference(resolution,[],[f1304,f1345])).

fof(f1345,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f1304,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1243,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1208])).

fof(f1208,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1207])).

fof(f1207,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1171])).

fof(f1171,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f1728,plain,(
    spl14_3 ),
    inference(avatar_contradiction_clause,[],[f1727])).

fof(f1727,plain,
    ( $false
    | spl14_3 ),
    inference(subsumption_resolution,[],[f1340,f1321])).

fof(f1321,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1266])).

fof(f1266,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1224])).

fof(f1224,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1223])).

fof(f1223,plain,(
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

fof(f1340,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl14_3 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f1339,plain,
    ( spl14_3
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f1726,plain,
    ( ~ spl14_2
    | ~ spl14_8
    | spl14_30 ),
    inference(avatar_contradiction_clause,[],[f1725])).

fof(f1725,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_8
    | spl14_30 ),
    inference(unit_resulting_resolution,[],[f1363,f1347,f1717,f1324])).

fof(f1324,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f1272])).

fof(f1272,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f1717,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl14_30 ),
    inference(avatar_component_clause,[],[f1716])).

fof(f1347,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1718,plain,
    ( ~ spl14_30
    | spl14_1
    | ~ spl14_7
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f1714,f1362,f1358,f1331,f1716])).

fof(f1714,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl14_1
    | ~ spl14_7
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f1713,f1363])).

fof(f1713,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | spl14_1
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f1706,f1359])).

fof(f1706,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_1 ),
    inference(resolution,[],[f1705,f1332])).

fof(f1332,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl14_1 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f1705,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f1704,f1291])).

fof(f1291,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f1198])).

fof(f1198,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1197])).

fof(f1197,plain,(
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

fof(f1704,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f1303,f1290])).

fof(f1290,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f1198])).

fof(f1303,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1364,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f1257,f1362])).

fof(f1257,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1222,plain,
    ( ( ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
        & sK0 != sK1 )
      | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    & ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
      | sK0 = sK1
      | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1220,f1221])).

fof(f1221,plain,
    ( ? [X0,X1,X2] :
        ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 )
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
          & sK0 != sK1 )
        | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
      & ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
        | sK0 = sK1
        | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1220,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1219])).

fof(f1219,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1180])).

fof(f1180,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1179])).

fof(f1179,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1173])).

fof(f1173,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
              | X0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1172])).

fof(f1172,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(f1360,plain,(
    spl14_7 ),
    inference(avatar_split_clause,[],[f1258,f1358])).

fof(f1258,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1356,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f1259,f1354])).

fof(f1259,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1352,plain,(
    spl14_5 ),
    inference(avatar_split_clause,[],[f1260,f1350])).

fof(f1260,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1348,plain,
    ( spl14_1
    | spl14_4
    | spl14_2 ),
    inference(avatar_split_clause,[],[f1261,f1334,f1342,f1331])).

fof(f1261,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1344,plain,
    ( ~ spl14_3
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f1337,f1342,f1339])).

fof(f1337,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    inference(inner_rewriting,[],[f1262])).

fof(f1262,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1336,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1263,f1334,f1331])).

fof(f1263,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f1222])).
%------------------------------------------------------------------------------
