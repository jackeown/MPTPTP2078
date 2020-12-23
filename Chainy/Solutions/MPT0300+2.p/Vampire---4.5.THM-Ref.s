%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0300+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 3.68s
% Output     : Refutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  394 (2379 expanded)
%              Number of leaves         :   91 ( 820 expanded)
%              Depth                    :   13
%              Number of atoms          : 1148 (10545 expanded)
%              Number of equality atoms :  129 (2114 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2568,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1151,f1170,f1171,f1190,f1191,f1207,f1208,f1209,f1228,f1229,f1242,f1243,f1244,f1278,f1281,f1283,f1287,f1288,f1289,f1395,f1402,f1403,f1404,f1408,f1409,f1410,f1556,f1558,f1560,f1562,f1564,f1566,f1568,f1570,f1572,f1574,f1576,f1578,f1580,f1582,f1586,f1588,f1590,f1592,f1593,f1594,f1595,f1660,f1664,f1804,f1806,f1808,f1810,f1812,f1814,f1816,f1818,f1820,f1822,f1824,f1826,f1828,f1830,f1919,f1920,f1973,f1977,f1984,f1991,f1998,f2033,f2040,f2041,f2042,f2049,f2056,f2058,f2059,f2061,f2062,f2102,f2106,f2113,f2120,f2127,f2134,f2149,f2156,f2428,f2435,f2442,f2446,f2453,f2477,f2484,f2491,f2495,f2519,f2523,f2530,f2554,f2558,f2567])).

fof(f2567,plain,(
    ~ spl39_47 ),
    inference(avatar_contradiction_clause,[],[f2566])).

fof(f2566,plain,
    ( $false
    | ~ spl39_47 ),
    inference(global_subsumption,[],[f692,f2152,f2564])).

fof(f2564,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl39_47 ),
    inference(resolution,[],[f2148,f798])).

fof(f798,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f611])).

fof(f611,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f610])).

fof(f610,plain,(
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

fof(f2148,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl39_47 ),
    inference(avatar_component_clause,[],[f2147])).

fof(f2147,plain,
    ( spl39_47
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_47])])).

fof(f2152,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f2150])).

fof(f2150,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f1311,f725])).

fof(f725,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f587])).

fof(f587,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f585,f586])).

fof(f586,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f585,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f584])).

fof(f584,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f410])).

fof(f410,plain,(
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

fof(f1311,plain,(
    ! [X16] :
      ( ~ r2_hidden(sK7(X16,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3))
      | r1_tarski(X16,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f1183,f726])).

fof(f726,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f587])).

fof(f1183,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(condensation,[],[f1182])).

fof(f1182,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(X14,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X14,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X14,k2_zfmisc_1(X12,X13)) ) ),
    inference(superposition,[],[f691,f1104])).

fof(f1104,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f752])).

fof(f752,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f606])).

fof(f606,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK13(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( sK13(X0,X1,X2) = k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2))
              & r2_hidden(sK15(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8
                & r2_hidden(sK17(X0,X1,X8),X1)
                & r2_hidden(sK16(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16,sK17])],[f602,f605,f604,f603])).

fof(f603,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK13(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK13(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f604,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK13(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK13(X0,X1,X2) = k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2))
        & r2_hidden(sK15(X0,X1,X2),X1)
        & r2_hidden(sK14(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f605,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8
        & r2_hidden(sK17(X0,X1,X8),X1)
        & r2_hidden(sK16(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f602,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f601])).

fof(f601,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f691,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f562])).

fof(f562,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
    & ! [X4,X5] :
        ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
          | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) )
        & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
          | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f560,f561])).

fof(f561,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
        & ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
              | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
            & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
              | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ) )
   => ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
      & ! [X5,X4] :
          ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) )
          & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f560,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      & ! [X4,X5] :
          ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
          & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ) ) ),
    inference(nnf_transformation,[],[f405])).

fof(f405,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      & ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f319])).

fof(f319,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
          <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
       => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(negated_conjecture,[],[f318])).

fof(f318,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
     => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_zfmisc_1)).

fof(f692,plain,(
    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f562])).

fof(f2558,plain,
    ( ~ spl39_68
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f2550,f1406,f2556])).

fof(f2556,plain,
    ( spl39_68
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_68])])).

fof(f1406,plain,
    ( spl39_17
  <=> ! [X8] :
        ( r2_hidden(X8,sK1)
        | ~ r2_hidden(X8,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_17])])).

fof(f2550,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl39_17 ),
    inference(duplicate_literal_removal,[],[f2546])).

fof(f2546,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK3)
    | ~ spl39_17 ),
    inference(resolution,[],[f1923,f1407])).

fof(f1407,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK1)
        | ~ r2_hidden(X8,sK3) )
    | ~ spl39_17 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f1923,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,X2)
        | ~ r2_hidden(X2,sK3) )
    | ~ spl39_17 ),
    inference(resolution,[],[f1407,f733])).

fof(f733,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f416])).

fof(f416,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2554,plain,
    ( ~ spl39_67
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f2540,f1406,f2552])).

fof(f2552,plain,
    ( spl39_67
  <=> r2_hidden(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_67])])).

fof(f2540,plain,
    ( ~ r2_hidden(k1_tarski(sK1),sK3)
    | ~ spl39_17 ),
    inference(resolution,[],[f1923,f1098])).

fof(f1098,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1097])).

fof(f1097,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f721])).

fof(f721,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f583])).

fof(f583,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f581,f582])).

fof(f582,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f581,plain,(
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
    inference(rectify,[],[f580])).

fof(f580,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f2530,plain,
    ( ~ spl39_65
    | ~ spl39_66
    | ~ spl39_13
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f2511,f1406,f1285,f2528,f2525])).

fof(f2525,plain,
    ( spl39_65
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_65])])).

fof(f2528,plain,
    ( spl39_66
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_66])])).

fof(f1285,plain,
    ( spl39_13
  <=> ! [X8] :
        ( r2_hidden(X8,sK0)
        | ~ r2_hidden(X8,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_13])])).

fof(f2511,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK3)
    | ~ spl39_13
    | ~ spl39_17 ),
    inference(resolution,[],[f1906,f1407])).

fof(f1906,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,X2)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl39_13 ),
    inference(resolution,[],[f1286,f733])).

fof(f1286,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK0)
        | ~ r2_hidden(X8,sK2) )
    | ~ spl39_13 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f2523,plain,
    ( ~ spl39_64
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f2515,f1285,f2521])).

fof(f2521,plain,
    ( spl39_64
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_64])])).

fof(f2515,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl39_13 ),
    inference(duplicate_literal_removal,[],[f2510])).

fof(f2510,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl39_13 ),
    inference(resolution,[],[f1906,f1286])).

fof(f2519,plain,
    ( ~ spl39_63
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f2505,f1285,f2517])).

fof(f2517,plain,
    ( spl39_63
  <=> r2_hidden(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_63])])).

fof(f2505,plain,
    ( ~ r2_hidden(k1_tarski(sK0),sK2)
    | ~ spl39_13 ),
    inference(resolution,[],[f1906,f1098])).

fof(f2495,plain,
    ( ~ spl39_62
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f2473,f1240,f2493])).

fof(f2493,plain,
    ( spl39_62
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_62])])).

fof(f1240,plain,
    ( spl39_10
  <=> ! [X2] :
        ( r2_hidden(X2,sK3)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_10])])).

fof(f2473,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl39_10 ),
    inference(duplicate_literal_removal,[],[f2471])).

fof(f2471,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK3,sK1)
    | ~ spl39_10 ),
    inference(resolution,[],[f1893,f1241])).

fof(f1241,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK3)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl39_10 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f1893,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl39_10 ),
    inference(resolution,[],[f1241,f733])).

fof(f2491,plain,
    ( ~ spl39_60
    | ~ spl39_61
    | ~ spl39_10
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f2469,f1406,f1240,f2489,f2486])).

fof(f2486,plain,
    ( spl39_60
  <=> r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_60])])).

fof(f2489,plain,
    ( spl39_61
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_61])])).

fof(f2469,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ r2_hidden(sK3,sK3)
    | ~ spl39_10
    | ~ spl39_17 ),
    inference(resolution,[],[f1893,f1407])).

fof(f2484,plain,
    ( ~ spl39_58
    | ~ spl39_59
    | ~ spl39_10
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f2468,f1285,f1240,f2482,f2479])).

fof(f2479,plain,
    ( spl39_58
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_58])])).

fof(f2482,plain,
    ( spl39_59
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_59])])).

fof(f2468,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK3,sK2)
    | ~ spl39_10
    | ~ spl39_13 ),
    inference(resolution,[],[f1893,f1286])).

fof(f2477,plain,
    ( ~ spl39_57
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f2463,f1240,f2475])).

fof(f2475,plain,
    ( spl39_57
  <=> r2_hidden(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_57])])).

fof(f2463,plain,
    ( ~ r2_hidden(k1_tarski(sK3),sK1)
    | ~ spl39_10 ),
    inference(resolution,[],[f1893,f1098])).

fof(f2453,plain,
    ( ~ spl39_55
    | ~ spl39_56
    | ~ spl39_7
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f2422,f1240,f1205,f2451,f2448])).

fof(f2448,plain,
    ( spl39_55
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_55])])).

fof(f2451,plain,
    ( spl39_56
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_56])])).

fof(f1205,plain,
    ( spl39_7
  <=> ! [X2] :
        ( r2_hidden(X2,sK2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_7])])).

fof(f2422,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl39_7
    | ~ spl39_10 ),
    inference(resolution,[],[f1212,f1241])).

fof(f1212,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,X2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl39_7 ),
    inference(resolution,[],[f1206,f733])).

fof(f1206,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl39_7 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f2446,plain,
    ( ~ spl39_54
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f2424,f1205,f2444])).

fof(f2444,plain,
    ( spl39_54
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_54])])).

fof(f2424,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl39_7 ),
    inference(duplicate_literal_removal,[],[f2421])).

fof(f2421,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK2,sK0)
    | ~ spl39_7 ),
    inference(resolution,[],[f1212,f1206])).

fof(f2442,plain,
    ( ~ spl39_52
    | ~ spl39_53
    | ~ spl39_7
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f2420,f1406,f1205,f2440,f2437])).

fof(f2437,plain,
    ( spl39_52
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_52])])).

fof(f2440,plain,
    ( spl39_53
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_53])])).

fof(f2420,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK2,sK3)
    | ~ spl39_7
    | ~ spl39_17 ),
    inference(resolution,[],[f1212,f1407])).

fof(f2435,plain,
    ( ~ spl39_50
    | ~ spl39_51
    | ~ spl39_7
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f2419,f1285,f1205,f2433,f2430])).

fof(f2430,plain,
    ( spl39_50
  <=> r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_50])])).

fof(f2433,plain,
    ( spl39_51
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_51])])).

fof(f2419,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK2,sK2)
    | ~ spl39_7
    | ~ spl39_13 ),
    inference(resolution,[],[f1212,f1286])).

fof(f2428,plain,
    ( ~ spl39_49
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f2414,f1205,f2426])).

fof(f2426,plain,
    ( spl39_49
  <=> r2_hidden(k1_tarski(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_49])])).

fof(f2414,plain,
    ( ~ r2_hidden(k1_tarski(sK2),sK0)
    | ~ spl39_7 ),
    inference(resolution,[],[f1212,f1098])).

fof(f2156,plain,(
    spl39_48 ),
    inference(avatar_split_clause,[],[f2152,f2154])).

fof(f2154,plain,
    ( spl39_48
  <=> r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_48])])).

fof(f2149,plain,(
    spl39_47 ),
    inference(avatar_split_clause,[],[f2145,f2147])).

fof(f2145,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f2143])).

fof(f2143,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f1253,f725])).

fof(f1253,plain,(
    ! [X12] :
      ( ~ r2_hidden(sK7(X12,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X12,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f1163,f726])).

fof(f1163,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(condensation,[],[f1162])).

fof(f1162,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(X14,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X14,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X14,k2_zfmisc_1(X12,X13)) ) ),
    inference(superposition,[],[f690,f1104])).

fof(f690,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f562])).

fof(f2134,plain,
    ( ~ spl39_45
    | ~ spl39_46
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f2096,f1240,f2132,f2129])).

fof(f2129,plain,
    ( spl39_45
  <=> r2_hidden(k2_zfmisc_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_45])])).

fof(f2132,plain,
    ( spl39_46
  <=> r2_hidden(sK3,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_46])])).

fof(f2096,plain,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK1)
    | ~ spl39_10 ),
    inference(resolution,[],[f1309,f1241])).

fof(f1309,plain,(
    ! [X14] :
      ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),X14)
      | ~ r2_hidden(X14,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f1183,f733])).

fof(f2127,plain,
    ( ~ spl39_43
    | ~ spl39_44
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f2095,f1205,f2125,f2122])).

fof(f2122,plain,
    ( spl39_43
  <=> r2_hidden(k2_zfmisc_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_43])])).

fof(f2125,plain,
    ( spl39_44
  <=> r2_hidden(sK2,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_44])])).

fof(f2095,plain,
    ( ~ r2_hidden(sK2,k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK0)
    | ~ spl39_7 ),
    inference(resolution,[],[f1309,f1206])).

fof(f2120,plain,
    ( ~ spl39_41
    | ~ spl39_42
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f2094,f1406,f2118,f2115])).

fof(f2115,plain,
    ( spl39_41
  <=> r2_hidden(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_41])])).

fof(f2118,plain,
    ( spl39_42
  <=> r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_42])])).

fof(f2094,plain,
    ( ~ r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3)
    | ~ spl39_17 ),
    inference(resolution,[],[f1309,f1407])).

fof(f2113,plain,
    ( ~ spl39_39
    | ~ spl39_40
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f2093,f1285,f2111,f2108])).

fof(f2108,plain,
    ( spl39_39
  <=> r2_hidden(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_39])])).

fof(f2111,plain,
    ( spl39_40
  <=> r2_hidden(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_40])])).

fof(f2093,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl39_13 ),
    inference(resolution,[],[f1309,f1286])).

fof(f2106,plain,(
    ~ spl39_38 ),
    inference(avatar_split_clause,[],[f2098,f2104])).

fof(f2104,plain,
    ( spl39_38
  <=> r2_hidden(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_38])])).

fof(f2098,plain,(
    ~ r2_hidden(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f2091])).

fof(f2091,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f1309,f1183])).

fof(f2102,plain,(
    ~ spl39_37 ),
    inference(avatar_split_clause,[],[f2088,f2100])).

fof(f2100,plain,
    ( spl39_37
  <=> r2_hidden(k1_tarski(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_37])])).

fof(f2088,plain,(
    ~ r2_hidden(k1_tarski(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f1309,f1098])).

fof(f2062,plain,
    ( ~ spl39_14
    | spl39_6
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f1891,f1240,f1202,f1393])).

fof(f1393,plain,
    ( spl39_14
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_14])])).

fof(f1202,plain,
    ( spl39_6
  <=> ! [X3] : ~ r2_hidden(X3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_6])])).

fof(f1891,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(sK3) )
    | ~ spl39_10 ),
    inference(resolution,[],[f1241,f912])).

fof(f912,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f643])).

fof(f643,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK25(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f641,f642])).

fof(f642,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK25(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f641,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f640])).

fof(f640,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2061,plain,
    ( ~ spl39_14
    | spl39_6
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f1892,f1240,f1202,f1393])).

fof(f1892,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ v1_xboole_0(sK3) )
    | ~ spl39_10 ),
    inference(resolution,[],[f1241,f906])).

fof(f906,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f482])).

fof(f482,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f2059,plain,
    ( ~ spl39_30
    | spl39_12
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f1921,f1406,f1276,f2031])).

fof(f2031,plain,
    ( spl39_30
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_30])])).

fof(f1276,plain,
    ( spl39_12
  <=> ! [X3] : ~ r2_hidden(X3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_12])])).

fof(f1921,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(sK1) )
    | ~ spl39_17 ),
    inference(resolution,[],[f1407,f912])).

fof(f2058,plain,
    ( ~ spl39_30
    | spl39_12
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f1922,f1406,f1276,f2031])).

fof(f1922,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | ~ v1_xboole_0(sK1) )
    | ~ spl39_17 ),
    inference(resolution,[],[f1407,f906])).

fof(f2056,plain,
    ( ~ spl39_35
    | ~ spl39_36
    | ~ spl39_17 ),
    inference(avatar_split_clause,[],[f1965,f1406,f2054,f2051])).

fof(f2051,plain,
    ( spl39_35
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_35])])).

fof(f2054,plain,
    ( spl39_36
  <=> r2_hidden(sK1,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_36])])).

fof(f1965,plain,
    ( ~ r2_hidden(sK1,k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK3)
    | ~ spl39_17 ),
    inference(resolution,[],[f1251,f1407])).

fof(f1251,plain,(
    ! [X10] :
      ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),X10)
      | ~ r2_hidden(X10,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f1163,f733])).

fof(f2049,plain,
    ( ~ spl39_33
    | ~ spl39_34
    | ~ spl39_10 ),
    inference(avatar_split_clause,[],[f1967,f1240,f2047,f2044])).

fof(f2044,plain,
    ( spl39_33
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_33])])).

fof(f2047,plain,
    ( spl39_34
  <=> r2_hidden(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_34])])).

fof(f1967,plain,
    ( ~ r2_hidden(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK1)
    | ~ spl39_10 ),
    inference(resolution,[],[f1251,f1241])).

fof(f2042,plain,
    ( spl39_32
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(avatar_split_clause,[],[f2023,f1393,f1240,f2038])).

fof(f2038,plain,
    ( spl39_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_32])])).

fof(f2023,plain,
    ( k1_xboole_0 = sK1
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(resolution,[],[f1903,f1008])).

fof(f1008,plain,(
    ! [X0] :
      ( r2_hidden(sK29(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f672])).

fof(f672,plain,(
    ! [X0] :
      ( r2_hidden(sK29(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29])],[f511,f671])).

fof(f671,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK29(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f511,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1903,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(global_subsumption,[],[f1394,f1891])).

fof(f1394,plain,
    ( v1_xboole_0(sK3)
    | ~ spl39_14 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f2041,plain,
    ( spl39_31
    | spl39_32
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(avatar_split_clause,[],[f2022,f1393,f1240,f2038,f2035])).

fof(f2035,plain,
    ( spl39_31
  <=> ! [X40] : sK1 = k1_tarski(X40) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_31])])).

fof(f2022,plain,
    ( ! [X41] :
        ( k1_xboole_0 = sK1
        | sK1 = k1_tarski(X41) )
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(resolution,[],[f1903,f983])).

fof(f983,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK28(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f661])).

fof(f661,plain,(
    ! [X0,X1] :
      ( ( sK28(X0,X1) != X1
        & r2_hidden(sK28(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28])],[f507,f660])).

fof(f660,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK28(X0,X1) != X1
        & r2_hidden(sK28(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f507,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f351])).

fof(f351,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f2040,plain,
    ( spl39_31
    | spl39_32
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(avatar_split_clause,[],[f2021,f1393,f1240,f2038,f2035])).

fof(f2021,plain,
    ( ! [X40] :
        ( k1_xboole_0 = sK1
        | sK1 = k1_tarski(X40) )
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(resolution,[],[f1903,f981])).

fof(f981,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK27(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f659])).

fof(f659,plain,(
    ! [X0,X1] :
      ( ( sK27(X0,X1) != X1
        & r2_hidden(sK27(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f506,f658])).

fof(f658,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK27(X0,X1) != X1
        & r2_hidden(sK27(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f506,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f2033,plain,
    ( spl39_30
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(avatar_split_clause,[],[f2016,f1393,f1240,f2031])).

fof(f2016,plain,
    ( v1_xboole_0(sK1)
    | ~ spl39_10
    | ~ spl39_14 ),
    inference(resolution,[],[f1903,f913])).

fof(f913,plain,(
    ! [X0] :
      ( r2_hidden(sK25(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f643])).

fof(f1998,plain,
    ( ~ spl39_28
    | ~ spl39_29
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f1966,f1205,f1996,f1993])).

fof(f1993,plain,
    ( spl39_28
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_28])])).

fof(f1996,plain,
    ( spl39_29
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_29])])).

fof(f1966,plain,
    ( ~ r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK0)
    | ~ spl39_7 ),
    inference(resolution,[],[f1251,f1206])).

fof(f1991,plain,
    ( ~ spl39_26
    | ~ spl39_27
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f1964,f1285,f1989,f1986])).

fof(f1986,plain,
    ( spl39_26
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_26])])).

fof(f1989,plain,
    ( spl39_27
  <=> r2_hidden(sK0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_27])])).

fof(f1964,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK2)
    | ~ spl39_13 ),
    inference(resolution,[],[f1251,f1286])).

fof(f1984,plain,
    ( ~ spl39_24
    | ~ spl39_25 ),
    inference(avatar_split_clause,[],[f1962,f1982,f1979])).

fof(f1979,plain,
    ( spl39_24
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_24])])).

fof(f1982,plain,
    ( spl39_25
  <=> r2_hidden(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_25])])).

fof(f1962,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f1251,f1183])).

fof(f1977,plain,(
    ~ spl39_23 ),
    inference(avatar_split_clause,[],[f1969,f1975])).

fof(f1975,plain,
    ( spl39_23
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_23])])).

fof(f1969,plain,(
    ~ r2_hidden(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1961])).

fof(f1961,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f1251,f1163])).

fof(f1973,plain,(
    ~ spl39_22 ),
    inference(avatar_split_clause,[],[f1959,f1971])).

fof(f1971,plain,
    ( spl39_22
  <=> r2_hidden(k1_tarski(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_22])])).

fof(f1959,plain,(
    ~ r2_hidden(k1_tarski(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f1251,f1098])).

fof(f1920,plain,
    ( ~ spl39_21
    | spl39_11
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f1905,f1285,f1273,f1917])).

fof(f1917,plain,
    ( spl39_21
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_21])])).

fof(f1273,plain,
    ( spl39_11
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_11])])).

fof(f1905,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(sK0) )
    | ~ spl39_13 ),
    inference(resolution,[],[f1286,f906])).

fof(f1919,plain,
    ( ~ spl39_21
    | spl39_11
    | ~ spl39_13 ),
    inference(avatar_split_clause,[],[f1904,f1285,f1273,f1917])).

fof(f1904,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(sK0) )
    | ~ spl39_13 ),
    inference(resolution,[],[f1286,f912])).

fof(f1830,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1829])).

fof(f1829,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1789,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(resolution,[],[f1753,f913])).

fof(f1753,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(condensation,[],[f1752])).

fof(f1752,plain,
    ( ! [X14,X12,X13] :
        ( ~ r2_hidden(X14,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X14,k2_zfmisc_1(X12,X13)) )
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(superposition,[],[f1655,f1104])).

fof(f1655,plain,
    ( ! [X4,X5] : ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f690,f1172,f1227])).

fof(f1227,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl39_9 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f1226,plain,
    ( spl39_9
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_9])])).

fof(f1172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f691,f746])).

fof(f746,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f600])).

fof(f600,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f599])).

fof(f599,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f310])).

fof(f310,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1186,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl39_4 ),
    inference(avatar_component_clause,[],[f1185])).

fof(f1185,plain,
    ( spl39_4
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_4])])).

fof(f1828,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1827])).

fof(f1827,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1826,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1825])).

fof(f1825,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1824,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1823])).

fof(f1823,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1822,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1821])).

fof(f1821,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1820,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1818,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1817])).

fof(f1817,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1816,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1815])).

fof(f1815,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1814,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1813])).

fof(f1813,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1812,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1811])).

fof(f1811,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1810,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1809])).

fof(f1809,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1808,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1807])).

fof(f1807,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1806,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1805])).

fof(f1805,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1804,plain,
    ( spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(avatar_contradiction_clause,[],[f1803])).

fof(f1803,plain,
    ( $false
    | spl39_4
    | ~ spl39_9
    | ~ spl39_16 ),
    inference(global_subsumption,[],[f1186,f1789])).

fof(f1664,plain,
    ( ~ spl39_20
    | spl39_2
    | ~ spl39_16 ),
    inference(avatar_split_clause,[],[f1606,f1400,f1165,f1662])).

fof(f1662,plain,
    ( spl39_20
  <=> v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_20])])).

fof(f1165,plain,
    ( spl39_2
  <=> v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_2])])).

fof(f1400,plain,
    ( spl39_16
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_16])])).

fof(f1606,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0))
    | spl39_2
    | ~ spl39_16 ),
    inference(backward_demodulation,[],[f1166,f1401])).

fof(f1401,plain,
    ( k1_xboole_0 = sK3
    | ~ spl39_16 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1166,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | spl39_2 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f1660,plain,
    ( ~ spl39_19
    | spl39_1
    | ~ spl39_16 ),
    inference(avatar_split_clause,[],[f1599,f1400,f1149,f1658])).

fof(f1658,plain,
    ( spl39_19
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_19])])).

fof(f1149,plain,
    ( spl39_1
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_1])])).

fof(f1599,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,k1_xboole_0)
    | spl39_1
    | ~ spl39_16 ),
    inference(backward_demodulation,[],[f1150,f1401])).

fof(f1150,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
    | spl39_1 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1595,plain,
    ( spl39_12
    | spl39_11
    | ~ spl39_9 ),
    inference(avatar_split_clause,[],[f1282,f1226,f1273,f1276])).

fof(f1282,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(X8,sK2)
        | ~ r2_hidden(X9,sK3) )
    | ~ spl39_9 ),
    inference(global_subsumption,[],[f1280])).

fof(f1280,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK2)
        | ~ r2_hidden(X7,sK3) )
    | ~ spl39_9 ),
    inference(global_subsumption,[],[f1271])).

fof(f1271,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,sK3)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl39_9 ),
    inference(global_subsumption,[],[f1227,f1262])).

fof(f1262,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f1172,f1103])).

fof(f1103,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f1102])).

fof(f1102,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f753])).

fof(f753,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f606])).

fof(f1594,plain,
    ( spl39_12
    | spl39_11
    | ~ spl39_9 ),
    inference(avatar_split_clause,[],[f1280,f1226,f1273,f1276])).

fof(f1593,plain,
    ( spl39_11
    | spl39_12
    | ~ spl39_9 ),
    inference(avatar_split_clause,[],[f1271,f1226,f1276,f1273])).

fof(f1592,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_split_clause,[],[f1541,f1273,f1223])).

fof(f1223,plain,
    ( spl39_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_8])])).

fof(f1541,plain,
    ( v1_xboole_0(sK2)
    | ~ spl39_11 ),
    inference(resolution,[],[f1274,f913])).

fof(f1274,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl39_11 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f1590,plain,
    ( spl39_18
    | ~ spl39_11 ),
    inference(avatar_split_clause,[],[f1589,f1273,f1584])).

fof(f1584,plain,
    ( spl39_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_18])])).

fof(f1589,plain,
    ( k1_xboole_0 = sK2
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1587])).

fof(f1587,plain,
    ( k1_xboole_0 = sK2
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1548])).

fof(f1548,plain,
    ( k1_xboole_0 = sK2
    | ~ spl39_11 ),
    inference(resolution,[],[f1274,f1008])).

fof(f1588,plain,
    ( spl39_18
    | ~ spl39_11 ),
    inference(avatar_split_clause,[],[f1587,f1273,f1584])).

fof(f1586,plain,
    ( spl39_18
    | ~ spl39_11 ),
    inference(avatar_split_clause,[],[f1548,f1273,f1584])).

fof(f1582,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1224,plain,
    ( ~ v1_xboole_0(sK2)
    | spl39_8 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f1580,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1579])).

fof(f1579,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1578,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1577])).

fof(f1577,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1576,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1575])).

fof(f1575,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1574,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1573])).

fof(f1573,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1572,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1571])).

fof(f1571,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1570,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1569])).

fof(f1569,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1568,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1567])).

fof(f1567,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1566,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1565])).

fof(f1565,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1564,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1563])).

fof(f1563,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1562,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1561])).

fof(f1561,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1560,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1559])).

fof(f1559,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1558,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1557])).

fof(f1557,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1556,plain,
    ( spl39_8
    | ~ spl39_11 ),
    inference(avatar_contradiction_clause,[],[f1555])).

fof(f1555,plain,
    ( $false
    | spl39_8
    | ~ spl39_11 ),
    inference(global_subsumption,[],[f1224,f1541])).

fof(f1410,plain,
    ( spl39_11
    | spl39_17 ),
    inference(avatar_split_clause,[],[f1291,f1406,f1273])).

fof(f1291,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f1173,f1103])).

fof(f1173,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f691,f747])).

fof(f747,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f600])).

fof(f1409,plain,
    ( spl39_11
    | spl39_17 ),
    inference(avatar_split_clause,[],[f1293,f1406,f1273])).

fof(f1293,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,sK1)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X7,sK2) ) ),
    inference(resolution,[],[f1173,f748])).

fof(f748,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f600])).

fof(f1408,plain,
    ( spl39_11
    | spl39_17 ),
    inference(avatar_split_clause,[],[f1294,f1406,f1273])).

fof(f1294,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,sK1)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK2) ) ),
    inference(resolution,[],[f1173,f745])).

fof(f745,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f598,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f597])).

fof(f597,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f316])).

fof(f316,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f1404,plain,
    ( spl39_16
    | ~ spl39_12 ),
    inference(avatar_split_clause,[],[f1385,f1276,f1400])).

fof(f1385,plain,
    ( k1_xboole_0 = sK3
    | ~ spl39_12 ),
    inference(resolution,[],[f1277,f1008])).

fof(f1277,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK3)
    | ~ spl39_12 ),
    inference(avatar_component_clause,[],[f1276])).

fof(f1403,plain,
    ( spl39_15
    | spl39_16
    | ~ spl39_12 ),
    inference(avatar_split_clause,[],[f1384,f1276,f1400,f1397])).

fof(f1397,plain,
    ( spl39_15
  <=> ! [X39] : sK3 = k1_tarski(X39) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_15])])).

fof(f1384,plain,
    ( ! [X40] :
        ( k1_xboole_0 = sK3
        | sK3 = k1_tarski(X40) )
    | ~ spl39_12 ),
    inference(resolution,[],[f1277,f983])).

fof(f1402,plain,
    ( spl39_15
    | spl39_16
    | ~ spl39_12 ),
    inference(avatar_split_clause,[],[f1383,f1276,f1400,f1397])).

fof(f1383,plain,
    ( ! [X39] :
        ( k1_xboole_0 = sK3
        | sK3 = k1_tarski(X39) )
    | ~ spl39_12 ),
    inference(resolution,[],[f1277,f981])).

fof(f1395,plain,
    ( spl39_14
    | ~ spl39_12 ),
    inference(avatar_split_clause,[],[f1378,f1276,f1393])).

fof(f1378,plain,
    ( v1_xboole_0(sK3)
    | ~ spl39_12 ),
    inference(resolution,[],[f1277,f913])).

fof(f1289,plain,
    ( spl39_12
    | spl39_13 ),
    inference(avatar_split_clause,[],[f1262,f1285,f1276])).

fof(f1288,plain,
    ( spl39_12
    | spl39_13 ),
    inference(avatar_split_clause,[],[f1264,f1285,f1276])).

fof(f1264,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,sK0)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2) ) ),
    inference(resolution,[],[f1172,f748])).

fof(f1287,plain,
    ( spl39_12
    | spl39_13 ),
    inference(avatar_split_clause,[],[f1265,f1285,f1276])).

fof(f1265,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,sK0)
      | ~ r2_hidden(X9,sK3)
      | ~ r2_hidden(X8,sK2) ) ),
    inference(resolution,[],[f1172,f745])).

fof(f1283,plain,
    ( spl39_12
    | spl39_11
    | ~ spl39_9 ),
    inference(avatar_split_clause,[],[f1282,f1226,f1273,f1276])).

fof(f1281,plain,
    ( spl39_12
    | spl39_11
    | ~ spl39_9 ),
    inference(avatar_split_clause,[],[f1280,f1226,f1273,f1276])).

fof(f1278,plain,
    ( spl39_11
    | spl39_12
    | ~ spl39_9 ),
    inference(avatar_split_clause,[],[f1271,f1226,f1276,f1273])).

fof(f1244,plain,
    ( spl39_9
    | spl39_10 ),
    inference(avatar_split_clause,[],[f1234,f1240,f1226])).

fof(f1234,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,sK3)
      | ~ r2_hidden(X8,sK1)
      | ~ r2_hidden(X9,sK0) ) ),
    inference(resolution,[],[f1153,f745])).

fof(f1153,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK3) ) ),
    inference(resolution,[],[f690,f747])).

fof(f1243,plain,
    ( spl39_9
    | spl39_10 ),
    inference(avatar_split_clause,[],[f1233,f1240,f1226])).

fof(f1233,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,sK3)
      | ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK0) ) ),
    inference(resolution,[],[f1153,f748])).

fof(f1242,plain,
    ( spl39_9
    | spl39_10 ),
    inference(avatar_split_clause,[],[f1231,f1240,f1226])).

fof(f1231,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK3)
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f1153,f1103])).

fof(f1229,plain,
    ( ~ spl39_8
    | spl39_9
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f1211,f1205,f1226,f1223])).

fof(f1211,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ v1_xboole_0(sK2) )
    | ~ spl39_7 ),
    inference(resolution,[],[f1206,f906])).

fof(f1228,plain,
    ( ~ spl39_8
    | spl39_9
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f1210,f1205,f1226,f1223])).

fof(f1210,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_xboole_0(sK2) )
    | ~ spl39_7 ),
    inference(resolution,[],[f1206,f912])).

fof(f1209,plain,
    ( spl39_6
    | spl39_7 ),
    inference(avatar_split_clause,[],[f1196,f1205,f1202])).

fof(f1196,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,sK2)
      | ~ r2_hidden(X9,sK1)
      | ~ r2_hidden(X8,sK0) ) ),
    inference(resolution,[],[f1152,f745])).

fof(f1152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f690,f746])).

fof(f1208,plain,
    ( spl39_6
    | spl39_7 ),
    inference(avatar_split_clause,[],[f1195,f1205,f1202])).

fof(f1195,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK1)
      | ~ r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f1152,f748])).

fof(f1207,plain,
    ( spl39_6
    | spl39_7 ),
    inference(avatar_split_clause,[],[f1193,f1205,f1202])).

fof(f1193,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f1152,f1103])).

fof(f1191,plain,
    ( ~ spl39_4
    | spl39_5 ),
    inference(avatar_split_clause,[],[f1177,f1188,f1185])).

fof(f1188,plain,
    ( spl39_5
  <=> ! [X9,X8] : ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_5])])).

fof(f1177,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK2,sK3))
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f691,f906])).

fof(f1190,plain,
    ( ~ spl39_4
    | spl39_5 ),
    inference(avatar_split_clause,[],[f1176,f1188,f1185])).

fof(f1176,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK2,sK3))
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f691,f912])).

fof(f1171,plain,
    ( ~ spl39_2
    | spl39_3 ),
    inference(avatar_split_clause,[],[f1157,f1168,f1165])).

fof(f1168,plain,
    ( spl39_3
  <=> ! [X9,X8] : ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_3])])).

fof(f1157,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
      | ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f690,f906])).

fof(f1170,plain,
    ( ~ spl39_2
    | spl39_3 ),
    inference(avatar_split_clause,[],[f1156,f1168,f1165])).

fof(f1156,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
      | ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f690,f912])).

fof(f1151,plain,(
    ~ spl39_1 ),
    inference(avatar_split_clause,[],[f692,f1149])).
%------------------------------------------------------------------------------
