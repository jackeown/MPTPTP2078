%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0911+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 300 expanded)
%              Number of leaves         :   25 ( 138 expanded)
%              Depth                    :   12
%              Number of atoms          :  550 (1292 expanded)
%              Number of equality atoms :  233 ( 611 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2051,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1503,f1507,f1511,f1515,f1519,f1754,f1768,f1782,f1796,f1811,f1825,f1839,f1895,f1949,f2003,f2009,f2050])).

fof(f2050,plain,
    ( spl14_19
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(avatar_contradiction_clause,[],[f2049])).

fof(f2049,plain,
    ( $false
    | spl14_19
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(subsumption_resolution,[],[f2047,f1810])).

fof(f1810,plain,
    ( sK3 != k2_mcart_1(sK4)
    | spl14_19 ),
    inference(avatar_component_clause,[],[f1809])).

fof(f1809,plain,
    ( spl14_19
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f2047,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(trivial_inequality_removal,[],[f2046])).

fof(f2046,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ spl14_24
    | ~ spl14_30 ),
    inference(superposition,[],[f1901,f2008])).

fof(f2008,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK3)
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f2007])).

fof(f2007,plain,
    ( spl14_30
  <=> sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f1901,plain,
    ( ! [X14,X12,X13] :
        ( sK4 != k3_mcart_1(X12,X13,X14)
        | k2_mcart_1(sK4) = X14 )
    | ~ spl14_24 ),
    inference(superposition,[],[f1453,f1894])).

fof(f1894,plain,
    ( sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f1893])).

fof(f1893,plain,
    ( spl14_24
  <=> sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f1453,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f1396,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1332])).

fof(f1332,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f2009,plain,
    ( spl14_30
    | ~ spl14_27
    | ~ spl14_29 ),
    inference(avatar_split_clause,[],[f2004,f2001,f1947,f2007])).

fof(f1947,plain,
    ( spl14_27
  <=> sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f2001,plain,
    ( spl14_29
  <=> sK3 = sK11(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_29])])).

fof(f2004,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK3)
    | ~ spl14_27
    | ~ spl14_29 ),
    inference(backward_demodulation,[],[f1948,f2002])).

fof(f2002,plain,
    ( sK3 = sK11(sK0,sK1,sK2,sK4)
    | ~ spl14_29 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f1948,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | ~ spl14_27 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f2003,plain,
    ( spl14_29
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_27 ),
    inference(avatar_split_clause,[],[f1999,f1947,f1780,f1766,f1752,f2001])).

fof(f1752,plain,
    ( spl14_13
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f1766,plain,
    ( spl14_14
  <=> m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f1780,plain,
    ( spl14_15
  <=> m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f1999,plain,
    ( sK3 = sK11(sK0,sK1,sK2,sK4)
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_27 ),
    inference(subsumption_resolution,[],[f1998,f1753])).

fof(f1753,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f1998,plain,
    ( sK3 = sK11(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_27 ),
    inference(subsumption_resolution,[],[f1997,f1767])).

fof(f1767,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f1997,plain,
    ( sK3 = sK11(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_15
    | ~ spl14_27 ),
    inference(subsumption_resolution,[],[f1996,f1781])).

fof(f1781,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1996,plain,
    ( sK3 = sK11(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_27 ),
    inference(trivial_inequality_removal,[],[f1966])).

fof(f1966,plain,
    ( sK4 != sK4
    | sK3 = sK11(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_27 ),
    inference(superposition,[],[f1426,f1948])).

fof(f1426,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f1408])).

fof(f1408,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1385,f1407])).

fof(f1407,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1385,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f1384])).

fof(f1384,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1380])).

fof(f1380,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1379])).

fof(f1379,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f1949,plain,
    ( spl14_27
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1945,f1517,f1513,f1509,f1505,f1947])).

fof(f1505,plain,
    ( spl14_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1509,plain,
    ( spl14_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f1513,plain,
    ( spl14_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f1517,plain,
    ( spl14_5
  <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f1945,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1944,f1514])).

fof(f1514,plain,
    ( k1_xboole_0 != sK0
    | spl14_4 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f1944,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1943,f1510])).

fof(f1510,plain,
    ( k1_xboole_0 != sK1
    | spl14_3 ),
    inference(avatar_component_clause,[],[f1509])).

fof(f1943,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1937,f1506])).

fof(f1506,plain,
    ( k1_xboole_0 != sK2
    | spl14_2 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f1937,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1463,f1518])).

fof(f1518,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f1463,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1418])).

fof(f1418,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK11(X0,X1,X2,X3),X2)
            & m1_subset_1(sK10(X0,X1,X2,X3),X1)
            & m1_subset_1(sK9(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f1397,f1417,f1416,f1415])).

fof(f1415,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK9(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK9(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1416,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK9(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK10(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1417,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK11(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f1397,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1299])).

fof(f1299,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f1895,plain,
    ( spl14_24
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16
    | ~ spl14_20
    | ~ spl14_21 ),
    inference(avatar_split_clause,[],[f1891,f1837,f1823,f1794,f1517,f1513,f1509,f1505,f1893])).

fof(f1794,plain,
    ( spl14_16
  <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f1823,plain,
    ( spl14_20
  <=> k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f1837,plain,
    ( spl14_21
  <=> k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).

fof(f1891,plain,
    ( sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16
    | ~ spl14_20
    | ~ spl14_21 ),
    inference(forward_demodulation,[],[f1890,f1824])).

fof(f1824,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f1890,plain,
    ( sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16
    | ~ spl14_21 ),
    inference(forward_demodulation,[],[f1889,f1838])).

fof(f1838,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl14_21 ),
    inference(avatar_component_clause,[],[f1837])).

fof(f1889,plain,
    ( sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k2_mcart_1(sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16 ),
    inference(forward_demodulation,[],[f1888,f1795])).

fof(f1795,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f1794])).

fof(f1888,plain,
    ( sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1887,f1514])).

fof(f1887,plain,
    ( sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1886,f1510])).

fof(f1886,plain,
    ( sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1880,f1506])).

fof(f1880,plain,
    ( sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1447,f1518])).

fof(f1447,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1393])).

fof(f1393,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1353])).

fof(f1353,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f1839,plain,
    ( spl14_21
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1835,f1517,f1513,f1509,f1505,f1837])).

fof(f1835,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1834,f1514])).

fof(f1834,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1833,f1510])).

fof(f1833,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1827,f1506])).

fof(f1827,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1442,f1518])).

fof(f1442,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1391,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1356])).

fof(f1356,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f1825,plain,
    ( spl14_20
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1821,f1517,f1513,f1509,f1505,f1823])).

fof(f1821,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1820,f1514])).

fof(f1820,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1819,f1510])).

fof(f1819,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1813,f1506])).

fof(f1813,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1441,f1518])).

fof(f1441,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1811,plain,
    ( ~ spl14_19
    | spl14_1
    | ~ spl14_16 ),
    inference(avatar_split_clause,[],[f1799,f1794,f1501,f1809])).

fof(f1501,plain,
    ( spl14_1
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f1799,plain,
    ( sK3 != k2_mcart_1(sK4)
    | spl14_1
    | ~ spl14_16 ),
    inference(superposition,[],[f1502,f1795])).

fof(f1502,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1796,plain,
    ( spl14_16
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1792,f1517,f1513,f1509,f1505,f1794])).

fof(f1792,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1791,f1514])).

fof(f1791,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1790,f1510])).

fof(f1790,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1784,f1506])).

fof(f1784,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1443,f1518])).

fof(f1443,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1782,plain,
    ( spl14_15
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1778,f1517,f1513,f1509,f1505,f1780])).

fof(f1778,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1777,f1514])).

fof(f1777,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1776,f1510])).

fof(f1776,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1770,f1506])).

fof(f1770,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1462,f1518])).

fof(f1462,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK11(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1418])).

fof(f1768,plain,
    ( spl14_14
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1764,f1517,f1513,f1509,f1505,f1766])).

fof(f1764,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1763,f1514])).

fof(f1763,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1762,f1510])).

fof(f1762,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1756,f1506])).

fof(f1756,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1461,f1518])).

fof(f1461,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK10(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1418])).

fof(f1754,plain,
    ( spl14_13
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1750,f1517,f1513,f1509,f1505,f1752])).

fof(f1750,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1749,f1514])).

fof(f1749,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1748,f1510])).

fof(f1748,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1742,f1506])).

fof(f1742,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1460,f1518])).

fof(f1460,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK9(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1418])).

fof(f1519,plain,(
    spl14_5 ),
    inference(avatar_split_clause,[],[f1425,f1517])).

fof(f1425,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1408])).

fof(f1515,plain,(
    ~ spl14_4 ),
    inference(avatar_split_clause,[],[f1427,f1513])).

fof(f1427,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1408])).

fof(f1511,plain,(
    ~ spl14_3 ),
    inference(avatar_split_clause,[],[f1428,f1509])).

fof(f1428,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1408])).

fof(f1507,plain,(
    ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1429,f1505])).

fof(f1429,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1408])).

fof(f1503,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f1430,f1501])).

fof(f1430,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f1408])).
%------------------------------------------------------------------------------
