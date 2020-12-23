%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0899+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 2.47s
% Output     : Refutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 226 expanded)
%              Number of leaves         :   26 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  717 (1337 expanded)
%              Number of equality atoms :  462 ( 960 expanded)
%              Maximal formula depth    :   19 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2861,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1504,f1508,f1512,f1516,f1520,f1524,f1528,f2592,f2688,f2701,f2860])).

fof(f2860,plain,
    ( spl29_1
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(avatar_contradiction_clause,[],[f2859])).

fof(f2859,plain,
    ( $false
    | spl29_1
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(subsumption_resolution,[],[f2858,f1527])).

fof(f1527,plain,
    ( k1_xboole_0 != sK0
    | spl29_10 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1526,plain,
    ( spl29_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_10])])).

fof(f2858,plain,
    ( k1_xboole_0 = sK0
    | spl29_1
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9 ),
    inference(subsumption_resolution,[],[f2857,f1523])).

fof(f1523,plain,
    ( k1_xboole_0 != sK1
    | spl29_9 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl29_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_9])])).

fof(f2857,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl29_1
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8 ),
    inference(subsumption_resolution,[],[f2856,f1519])).

fof(f1519,plain,
    ( k1_xboole_0 != sK2
    | spl29_8 ),
    inference(avatar_component_clause,[],[f1518])).

fof(f1518,plain,
    ( spl29_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_8])])).

fof(f2856,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl29_1
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7 ),
    inference(subsumption_resolution,[],[f2855,f1515])).

fof(f1515,plain,
    ( k1_xboole_0 != sK3
    | spl29_7 ),
    inference(avatar_component_clause,[],[f1514])).

fof(f1514,plain,
    ( spl29_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_7])])).

fof(f2855,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl29_1
    | ~ spl29_5
    | ~ spl29_6 ),
    inference(subsumption_resolution,[],[f2848,f1494])).

fof(f1494,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5
    | spl29_1 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1493,plain,
    ( spl29_1
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).

fof(f2848,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6 ),
    inference(resolution,[],[f1905,f1511])).

fof(f1511,plain,
    ( m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl29_6 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f1510,plain,
    ( spl29_6
  <=> m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_6])])).

fof(f1905,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl29_5 ),
    inference(superposition,[],[f1888,f1507])).

fof(f1507,plain,
    ( sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    | ~ spl29_5 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1506,plain,
    ( spl29_5
  <=> sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_5])])).

fof(f1888,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1487,f1441])).

fof(f1441,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f1378])).

fof(f1378,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1296])).

fof(f1296,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f1487,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1486])).

fof(f1486,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1442])).

fof(f1442,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1411])).

fof(f1411,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK21(X4,X5) != X5
                    & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22,sK23,sK24])],[f1409,f1410])).

fof(f1410,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK21(X4,X5) != X5
        & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f1409,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1408])).

fof(f1408,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1379])).

fof(f1379,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1283])).

fof(f1283,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X6 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_mcart_1)).

fof(f2701,plain,
    ( spl29_2
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(avatar_split_clause,[],[f2699,f1526,f1522,f1518,f1514,f1510,f1506,f1496])).

fof(f1496,plain,
    ( spl29_2
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_2])])).

fof(f2699,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(subsumption_resolution,[],[f2698,f1527])).

fof(f2698,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9 ),
    inference(subsumption_resolution,[],[f2697,f1523])).

fof(f2697,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8 ),
    inference(subsumption_resolution,[],[f2696,f1519])).

fof(f2696,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7 ),
    inference(subsumption_resolution,[],[f2690,f1515])).

fof(f2690,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6 ),
    inference(resolution,[],[f1874,f1511])).

fof(f1874,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl29_5 ),
    inference(superposition,[],[f1868,f1507])).

fof(f1868,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1485,f1437])).

fof(f1437,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f1376])).

fof(f1376,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f1485,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1484])).

fof(f1484,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1438])).

fof(f1438,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK18(X4,X5) != X5
                    & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19,sK20])],[f1405,f1406])).

fof(f1406,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK18(X4,X5) != X5
        & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f1405,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1404])).

fof(f1404,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1377])).

fof(f1377,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1284])).

fof(f1284,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_mcart_1)).

fof(f2688,plain,
    ( spl29_3
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(avatar_split_clause,[],[f2686,f1526,f1522,f1518,f1514,f1510,f1506,f1499])).

fof(f1499,plain,
    ( spl29_3
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).

fof(f2686,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(subsumption_resolution,[],[f2685,f1527])).

fof(f2685,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9 ),
    inference(subsumption_resolution,[],[f2684,f1523])).

fof(f2684,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8 ),
    inference(subsumption_resolution,[],[f2683,f1519])).

fof(f2683,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7 ),
    inference(subsumption_resolution,[],[f2677,f1515])).

fof(f2677,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6 ),
    inference(resolution,[],[f1849,f1511])).

fof(f1849,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl29_5 ),
    inference(superposition,[],[f1840,f1507])).

fof(f1840,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1483,f1433])).

fof(f1433,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f1374])).

fof(f1374,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f1483,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1482])).

fof(f1482,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1434])).

fof(f1434,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1403])).

fof(f1403,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK15(X4,X5) != X5
                    & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f1401,f1402])).

fof(f1402,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK15(X4,X5) != X5
        & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f1401,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1400])).

fof(f1400,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1375])).

fof(f1375,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1272])).

fof(f1272,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X8 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_mcart_1)).

fof(f2592,plain,
    ( spl29_4
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(avatar_split_clause,[],[f2590,f1526,f1522,f1518,f1514,f1510,f1506,f1502])).

fof(f1502,plain,
    ( spl29_4
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f2590,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9
    | spl29_10 ),
    inference(subsumption_resolution,[],[f2589,f1527])).

fof(f2589,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8
    | spl29_9 ),
    inference(subsumption_resolution,[],[f2588,f1523])).

fof(f2588,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7
    | spl29_8 ),
    inference(subsumption_resolution,[],[f2587,f1519])).

fof(f2587,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6
    | spl29_7 ),
    inference(subsumption_resolution,[],[f2581,f1515])).

fof(f2581,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl29_5
    | ~ spl29_6 ),
    inference(resolution,[],[f1822,f1511])).

fof(f1822,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl29_5 ),
    inference(superposition,[],[f1814,f1507])).

fof(f1814,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1481,f1429])).

fof(f1429,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f1372])).

fof(f1372,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f1481,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1480])).

fof(f1480,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1430])).

fof(f1430,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK12(X4,X5) != X5
                    & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f1397,f1398])).

fof(f1398,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X9
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK12(X4,X5) != X5
        & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f1397,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1396])).

fof(f1396,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1373])).

fof(f1373,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1273])).

fof(f1273,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X9 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_mcart_1)).

fof(f1528,plain,(
    ~ spl29_10 ),
    inference(avatar_split_clause,[],[f1422,f1526])).

fof(f1422,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1395])).

fof(f1395,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
    & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f1371,f1394,f1393,f1392])).

fof(f1392,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ? [X8,X7,X6,X5] :
              ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X4) != X8
                | k10_mcart_1(sK0,sK1,sK2,sK3,X4) != X7
                | k9_mcart_1(sK0,sK1,sK2,sK3,X4) != X6
                | k8_mcart_1(sK0,sK1,sK2,sK3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f1393,plain,
    ( ? [X4] :
        ( ? [X8,X7,X6,X5] :
            ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X4) != X8
              | k10_mcart_1(sK0,sK1,sK2,sK3,X4) != X7
              | k9_mcart_1(sK0,sK1,sK2,sK3,X4) != X6
              | k8_mcart_1(sK0,sK1,sK2,sK3,X4) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = X4 )
        & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
            | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
            | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
            | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK4 )
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f1394,plain,
    ( ? [X8,X7,X6,X5] :
        ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
          | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
          | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
          | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
        & k4_mcart_1(X5,X6,X7,X8) = sK4 )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
      & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f1371,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1365])).

fof(f1365,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ? [X4] :
              ( ? [X5,X6,X7,X8] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                      & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                      & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                      & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                  & k4_mcart_1(X5,X6,X7,X8) = X4 )
              & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1364])).

fof(f1364,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f1524,plain,(
    ~ spl29_9 ),
    inference(avatar_split_clause,[],[f1423,f1522])).

fof(f1423,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1395])).

fof(f1520,plain,(
    ~ spl29_8 ),
    inference(avatar_split_clause,[],[f1424,f1518])).

fof(f1424,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1395])).

fof(f1516,plain,(
    ~ spl29_7 ),
    inference(avatar_split_clause,[],[f1425,f1514])).

fof(f1425,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1395])).

fof(f1512,plain,(
    spl29_6 ),
    inference(avatar_split_clause,[],[f1426,f1510])).

fof(f1426,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1508,plain,(
    spl29_5 ),
    inference(avatar_split_clause,[],[f1427,f1506])).

fof(f1427,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1504,plain,
    ( ~ spl29_1
    | ~ spl29_2
    | ~ spl29_3
    | ~ spl29_4 ),
    inference(avatar_split_clause,[],[f1428,f1502,f1499,f1496,f1493])).

fof(f1428,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f1395])).
%------------------------------------------------------------------------------
