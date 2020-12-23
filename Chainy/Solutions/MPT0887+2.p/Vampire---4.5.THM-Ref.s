%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0887+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 165 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  481 ( 887 expanded)
%              Number of equality atoms :  305 ( 626 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1464,f1468,f1472,f1476,f1480,f1484,f2226,f2242,f2264])).

fof(f2264,plain,
    ( spl20_1
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7
    | spl20_8 ),
    inference(avatar_contradiction_clause,[],[f2263])).

fof(f2263,plain,
    ( $false
    | spl20_1
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7
    | spl20_8 ),
    inference(subsumption_resolution,[],[f2262,f1483])).

fof(f1483,plain,
    ( k1_xboole_0 != sK0
    | spl20_8 ),
    inference(avatar_component_clause,[],[f1482])).

fof(f1482,plain,
    ( spl20_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_8])])).

fof(f2262,plain,
    ( k1_xboole_0 = sK0
    | spl20_1
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7 ),
    inference(subsumption_resolution,[],[f2261,f1479])).

fof(f1479,plain,
    ( k1_xboole_0 != sK1
    | spl20_7 ),
    inference(avatar_component_clause,[],[f1478])).

fof(f1478,plain,
    ( spl20_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_7])])).

fof(f2261,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl20_1
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6 ),
    inference(subsumption_resolution,[],[f2260,f1475])).

fof(f1475,plain,
    ( k1_xboole_0 != sK2
    | spl20_6 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f1474,plain,
    ( spl20_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_6])])).

fof(f2260,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl20_1
    | ~ spl20_4
    | ~ spl20_5 ),
    inference(subsumption_resolution,[],[f2253,f1457])).

fof(f1457,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) != sK4
    | spl20_1 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f1456,plain,
    ( spl20_1
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f2253,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5 ),
    inference(resolution,[],[f1881,f1471])).

fof(f1471,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl20_5 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f1470,plain,
    ( spl20_5
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_5])])).

fof(f1881,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
        | sK4 = k5_mcart_1(X0,X1,X2,sK3)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl20_4 ),
    inference(superposition,[],[f1872,f1467])).

fof(f1467,plain,
    ( sK3 = k3_mcart_1(sK4,sK5,sK6)
    | ~ spl20_4 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1466,plain,
    ( spl20_4
  <=> sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).

fof(f1872,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X8
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1451,f1407])).

fof(f1407,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f1353])).

fof(f1353,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f1451,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X8
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1450])).

fof(f1450,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X8
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1408])).

fof(f1408,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X8
      | k3_mcart_1(X8,X9,X10) != X3
      | k5_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1382])).

fof(f1382,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK13(X3,X4) != X4
                    & k3_mcart_1(sK13(X3,X4),sK14(X3,X4),sK15(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f1380,f1381])).

fof(f1381,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK13(X3,X4) != X4
        & k3_mcart_1(sK13(X3,X4),sK14(X3,X4),sK15(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f1380,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1379])).

fof(f1379,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X5
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1354])).

fof(f1354,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1277])).

fof(f1277,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_mcart_1)).

fof(f2242,plain,
    ( spl20_2
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7
    | spl20_8 ),
    inference(avatar_split_clause,[],[f2240,f1482,f1478,f1474,f1470,f1466,f1459])).

fof(f1459,plain,
    ( spl20_2
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_2])])).

fof(f2240,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK5
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7
    | spl20_8 ),
    inference(subsumption_resolution,[],[f2239,f1483])).

fof(f2239,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK5
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7 ),
    inference(subsumption_resolution,[],[f2238,f1479])).

fof(f2238,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK5
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6 ),
    inference(subsumption_resolution,[],[f2232,f1475])).

fof(f2232,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK5
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5 ),
    inference(resolution,[],[f1861,f1471])).

fof(f1861,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
        | sK5 = k6_mcart_1(X0,X1,X2,sK3)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl20_4 ),
    inference(superposition,[],[f1853,f1467])).

fof(f1853,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1449,f1403])).

fof(f1403,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f1351])).

fof(f1351,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f1449,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1448])).

fof(f1448,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X9
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1404])).

fof(f1404,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k3_mcart_1(X8,X9,X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1378])).

fof(f1378,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK11(X3,X4) != X4
                    & k3_mcart_1(sK10(X3,X4),sK11(X3,X4),sK12(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f1376,f1377])).

fof(f1377,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK11(X3,X4) != X4
        & k3_mcart_1(sK10(X3,X4),sK11(X3,X4),sK12(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f1376,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1375])).

fof(f1375,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X6
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1352])).

fof(f1352,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k6_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X6
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1278])).

fof(f1278,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( k6_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X6 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).

fof(f2226,plain,
    ( spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7
    | spl20_8 ),
    inference(avatar_split_clause,[],[f2224,f1482,f1478,f1474,f1470,f1466,f1462])).

fof(f1462,plain,
    ( spl20_3
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f2224,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK6
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7
    | spl20_8 ),
    inference(subsumption_resolution,[],[f2223,f1483])).

fof(f2223,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK6
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | spl20_7 ),
    inference(subsumption_resolution,[],[f2222,f1479])).

fof(f2222,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK6
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6 ),
    inference(subsumption_resolution,[],[f2216,f1475])).

fof(f2216,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK6
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl20_4
    | ~ spl20_5 ),
    inference(resolution,[],[f1842,f1471])).

fof(f1842,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
        | sK6 = k7_mcart_1(X0,X1,X2,sK3)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl20_4 ),
    inference(superposition,[],[f1840,f1467])).

fof(f1840,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1447,f1399])).

fof(f1399,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f1349])).

fof(f1349,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1287])).

fof(f1287,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f1447,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1446])).

fof(f1446,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X10
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1400])).

fof(f1400,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k3_mcart_1(X8,X9,X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1374])).

fof(f1374,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK9(X3,X4) != X4
                    & k3_mcart_1(sK7(X3,X4),sK8(X3,X4),sK9(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f1372,f1373])).

fof(f1373,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X7
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK9(X3,X4) != X4
        & k3_mcart_1(sK7(X3,X4),sK8(X3,X4),sK9(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f1372,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X7
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1371])).

fof(f1371,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X7
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X7
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1350])).

fof(f1350,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X7
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1279])).

fof(f1279,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ( k7_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X7 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_mcart_1)).

fof(f1484,plain,(
    ~ spl20_8 ),
    inference(avatar_split_clause,[],[f1393,f1482])).

fof(f1393,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1370])).

fof(f1370,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
      | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
      | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 )
    & sK3 = k3_mcart_1(sK4,sK5,sK6)
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f1348,f1369,f1368,f1367])).

fof(f1367,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                  | k6_mcart_1(X0,X1,X2,X3) != X5
                  | k5_mcart_1(X0,X1,X2,X3) != X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ? [X6,X5,X4] :
              ( ( k7_mcart_1(sK0,sK1,sK2,X3) != X6
                | k6_mcart_1(sK0,sK1,sK2,X3) != X5
                | k5_mcart_1(sK0,sK1,sK2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f1368,plain,
    ( ? [X3] :
        ( ? [X6,X5,X4] :
            ( ( k7_mcart_1(sK0,sK1,sK2,X3) != X6
              | k6_mcart_1(sK0,sK1,sK2,X3) != X5
              | k5_mcart_1(sK0,sK1,sK2,X3) != X4 )
            & k3_mcart_1(X4,X5,X6) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ? [X6,X5,X4] :
          ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != X6
            | k6_mcart_1(sK0,sK1,sK2,sK3) != X5
            | k5_mcart_1(sK0,sK1,sK2,sK3) != X4 )
          & k3_mcart_1(X4,X5,X6) = sK3 )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1369,plain,
    ( ? [X6,X5,X4] :
        ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != X6
          | k6_mcart_1(sK0,sK1,sK2,sK3) != X5
          | k5_mcart_1(sK0,sK1,sK2,sK3) != X4 )
        & k3_mcart_1(X4,X5,X6) = sK3 )
   => ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
        | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
        | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 )
      & sK3 = k3_mcart_1(sK4,sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f1348,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                | k6_mcart_1(X0,X1,X2,X3) != X5
                | k5_mcart_1(X0,X1,X2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1341])).

fof(f1341,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ? [X3] :
              ( ? [X4,X5,X6] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                      & k6_mcart_1(X0,X1,X2,X3) = X5
                      & k5_mcart_1(X0,X1,X2,X3) = X4 )
                  & k3_mcart_1(X4,X5,X6) = X3 )
              & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1340])).

fof(f1340,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

fof(f1480,plain,(
    ~ spl20_7 ),
    inference(avatar_split_clause,[],[f1394,f1478])).

fof(f1394,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1370])).

fof(f1476,plain,(
    ~ spl20_6 ),
    inference(avatar_split_clause,[],[f1395,f1474])).

fof(f1395,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1370])).

fof(f1472,plain,(
    spl20_5 ),
    inference(avatar_split_clause,[],[f1396,f1470])).

fof(f1396,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1370])).

fof(f1468,plain,(
    spl20_4 ),
    inference(avatar_split_clause,[],[f1397,f1466])).

fof(f1397,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f1370])).

fof(f1464,plain,
    ( ~ spl20_1
    | ~ spl20_2
    | ~ spl20_3 ),
    inference(avatar_split_clause,[],[f1398,f1462,f1459,f1456])).

fof(f1398,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
    | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
    | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f1370])).
%------------------------------------------------------------------------------
