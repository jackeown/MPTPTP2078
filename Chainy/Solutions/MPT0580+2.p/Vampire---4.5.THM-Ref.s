%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0580+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 3.38s
% Output     : Refutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 156 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 ( 586 expanded)
%              Number of equality atoms :   68 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5841,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1492,f1506,f1516,f1530,f1704,f5393,f5398,f5539,f5549,f5840])).

fof(f5840,plain,
    ( spl33_4
    | ~ spl33_6
    | ~ spl33_21 ),
    inference(avatar_contradiction_clause,[],[f5839])).

fof(f5839,plain,
    ( $false
    | spl33_4
    | ~ spl33_6
    | ~ spl33_21 ),
    inference(subsumption_resolution,[],[f5700,f5572])).

fof(f5572,plain,
    ( ~ r2_hidden(sK1,k1_tarski(k1_xboole_0))
    | spl33_4 ),
    inference(unit_resulting_resolution,[],[f1505,f1437])).

fof(f1437,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f1176])).

fof(f1176,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f1041,f1042])).

fof(f1042,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1041,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f1040])).

fof(f1040,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1505,plain,
    ( k1_xboole_0 != sK1
    | spl33_4 ),
    inference(avatar_component_clause,[],[f1503])).

fof(f1503,plain,
    ( spl33_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_4])])).

fof(f5700,plain,
    ( r2_hidden(sK1,k1_tarski(k1_xboole_0))
    | ~ spl33_6
    | ~ spl33_21 ),
    inference(unit_resulting_resolution,[],[f1515,f1702,f1160])).

fof(f1160,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1033])).

fof(f1033,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f1031,f1032])).

fof(f1032,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1031,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1030])).

fof(f1030,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f857])).

fof(f857,plain,(
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

fof(f1702,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | ~ spl33_21 ),
    inference(avatar_component_clause,[],[f1701])).

fof(f1701,plain,
    ( spl33_21
  <=> r1_tarski(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_21])])).

fof(f1515,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl33_6 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f1513,plain,
    ( spl33_6
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_6])])).

fof(f5549,plain,
    ( ~ spl33_1
    | ~ spl33_3
    | spl33_21 ),
    inference(avatar_contradiction_clause,[],[f5548])).

fof(f5548,plain,
    ( $false
    | ~ spl33_1
    | ~ spl33_3
    | spl33_21 ),
    inference(subsumption_resolution,[],[f1500,f1705])).

fof(f1705,plain,
    ( ~ v3_relat_1(sK0)
    | ~ spl33_1
    | spl33_21 ),
    inference(unit_resulting_resolution,[],[f1491,f1703,f1170])).

fof(f1170,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1037])).

fof(f1037,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f865])).

fof(f865,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f1703,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | spl33_21 ),
    inference(avatar_component_clause,[],[f1701])).

fof(f1491,plain,
    ( v1_relat_1(sK0)
    | ~ spl33_1 ),
    inference(avatar_component_clause,[],[f1489])).

fof(f1489,plain,
    ( spl33_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_1])])).

fof(f1500,plain,
    ( v3_relat_1(sK0)
    | ~ spl33_3 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1499,plain,
    ( spl33_3
  <=> v3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_3])])).

fof(f5539,plain,
    ( ~ spl33_9
    | spl33_50
    | ~ spl33_51 ),
    inference(avatar_contradiction_clause,[],[f5538])).

fof(f5538,plain,
    ( $false
    | ~ spl33_9
    | spl33_50
    | ~ spl33_51 ),
    inference(subsumption_resolution,[],[f5537,f1431])).

fof(f1431,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1142])).

fof(f1142,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f1021])).

fof(f1021,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f1020])).

fof(f1020,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f397])).

fof(f397,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f5537,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl33_9
    | spl33_50
    | ~ spl33_51 ),
    inference(forward_demodulation,[],[f5509,f1430])).

fof(f1430,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f5509,plain,
    ( ~ r1_tarski(k2_tarski(k1_xboole_0,k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl33_9
    | spl33_50
    | ~ spl33_51 ),
    inference(backward_demodulation,[],[f5463,f5464])).

fof(f5464,plain,
    ( k1_xboole_0 = sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | ~ spl33_9
    | ~ spl33_51 ),
    inference(unit_resulting_resolution,[],[f5397,f1529])).

fof(f1529,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK0))
        | k1_xboole_0 = X2 )
    | ~ spl33_9 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f1528,plain,
    ( spl33_9
  <=> ! [X2] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X2,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_9])])).

fof(f5397,plain,
    ( r2_hidden(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)),k2_relat_1(sK0))
    | ~ spl33_51 ),
    inference(avatar_component_clause,[],[f5395])).

fof(f5395,plain,
    ( spl33_51
  <=> r2_hidden(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_51])])).

fof(f5463,plain,
    ( ~ r1_tarski(k2_tarski(k1_xboole_0,sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0))),k1_tarski(k1_xboole_0))
    | spl33_50 ),
    inference(forward_demodulation,[],[f5462,f1424])).

fof(f1424,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f5462,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)))),k1_tarski(k1_xboole_0))
    | spl33_50 ),
    inference(forward_demodulation,[],[f5444,f1207])).

fof(f1207,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5444,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0))),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | spl33_50 ),
    inference(unit_resulting_resolution,[],[f5392,f1181])).

fof(f1181,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f867])).

fof(f867,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f303])).

fof(f303,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(f5392,plain,
    ( ~ r2_hidden(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | spl33_50 ),
    inference(avatar_component_clause,[],[f5390])).

fof(f5390,plain,
    ( spl33_50
  <=> r2_hidden(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_50])])).

fof(f5398,plain,
    ( spl33_51
    | spl33_21 ),
    inference(avatar_split_clause,[],[f1707,f1701,f5395])).

fof(f1707,plain,
    ( r2_hidden(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)),k2_relat_1(sK0))
    | spl33_21 ),
    inference(unit_resulting_resolution,[],[f1703,f1161])).

fof(f1161,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1033])).

fof(f5393,plain,
    ( ~ spl33_50
    | spl33_21 ),
    inference(avatar_split_clause,[],[f1706,f1701,f5390])).

fof(f1706,plain,
    ( ~ r2_hidden(sK7(k2_relat_1(sK0),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | spl33_21 ),
    inference(unit_resulting_resolution,[],[f1703,f1162])).

fof(f1162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1033])).

fof(f1704,plain,
    ( ~ spl33_21
    | ~ spl33_1
    | spl33_3 ),
    inference(avatar_split_clause,[],[f1644,f1499,f1489,f1701])).

fof(f1644,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | ~ spl33_1
    | spl33_3 ),
    inference(unit_resulting_resolution,[],[f1491,f1501,f1171])).

fof(f1171,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1037])).

fof(f1501,plain,
    ( ~ v3_relat_1(sK0)
    | spl33_3 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1530,plain,
    ( spl33_3
    | spl33_9 ),
    inference(avatar_split_clause,[],[f1124,f1528,f1499])).

fof(f1124,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK0))
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f1015])).

fof(f1015,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1012,f1014,f1013])).

fof(f1013,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1014,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1012,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f1011])).

fof(f1011,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1010])).

fof(f1010,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f844])).

fof(f844,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f772])).

fof(f772,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f771])).

fof(f771,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f1516,plain,
    ( ~ spl33_3
    | spl33_6 ),
    inference(avatar_split_clause,[],[f1125,f1513,f1499])).

fof(f1125,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1015])).

fof(f1506,plain,
    ( ~ spl33_3
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f1126,f1503,f1499])).

fof(f1126,plain,
    ( k1_xboole_0 != sK1
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1015])).

fof(f1492,plain,(
    spl33_1 ),
    inference(avatar_split_clause,[],[f1123,f1489])).

fof(f1123,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1015])).
%------------------------------------------------------------------------------
