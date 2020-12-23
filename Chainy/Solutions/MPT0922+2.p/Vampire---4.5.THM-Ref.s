%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0922+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 393 expanded)
%              Number of leaves         :   31 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  790 (1854 expanded)
%              Number of equality atoms :  321 ( 863 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1528,f1532,f1536,f1540,f1544,f1548,f1655,f1875,f1891,f1907,f1939,f1946,f1954,f1970,f1986,f2002,f2079,f2123,f2319,f2372,f2457])).

fof(f2457,plain,
    ( spl17_35
    | ~ spl17_29
    | ~ spl17_33 ),
    inference(avatar_split_clause,[],[f2431,f2121,f2077,f2168])).

fof(f2168,plain,
    ( spl17_35
  <=> sK14(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_35])])).

fof(f2077,plain,
    ( spl17_29
  <=> sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_29])])).

fof(f2121,plain,
    ( spl17_33
  <=> sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_33])])).

fof(f2431,plain,
    ( sK14(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | ~ spl17_29
    | ~ spl17_33 ),
    inference(trivial_inequality_removal,[],[f2430])).

fof(f2430,plain,
    ( sK5 != sK5
    | sK14(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | ~ spl17_29
    | ~ spl17_33 ),
    inference(superposition,[],[f2087,f2122])).

fof(f2122,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5))
    | ~ spl17_33 ),
    inference(avatar_component_clause,[],[f2121])).

fof(f2087,plain,
    ( ! [X26,X24,X27,X25] :
        ( sK5 != k4_mcart_1(X24,X25,X26,X27)
        | k2_mcart_1(sK5) = X27 )
    | ~ spl17_29 ),
    inference(superposition,[],[f1471,f2078])).

fof(f2078,plain,
    ( sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))
    | ~ spl17_29 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f1471,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1337])).

fof(f1337,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f2372,plain,
    ( ~ spl17_15
    | ~ spl17_16
    | ~ spl17_17
    | ~ spl17_20
    | spl17_22
    | ~ spl17_47 ),
    inference(avatar_contradiction_clause,[],[f2371])).

fof(f2371,plain,
    ( $false
    | ~ spl17_15
    | ~ spl17_16
    | ~ spl17_17
    | ~ spl17_20
    | spl17_22
    | ~ spl17_47 ),
    inference(subsumption_resolution,[],[f2370,f1874])).

fof(f1874,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl17_15 ),
    inference(avatar_component_clause,[],[f1873])).

fof(f1873,plain,
    ( spl17_15
  <=> m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f2370,plain,
    ( ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl17_16
    | ~ spl17_17
    | ~ spl17_20
    | spl17_22
    | ~ spl17_47 ),
    inference(subsumption_resolution,[],[f2369,f1890])).

fof(f1890,plain,
    ( m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ spl17_16 ),
    inference(avatar_component_clause,[],[f1889])).

fof(f1889,plain,
    ( spl17_16
  <=> m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).

fof(f2369,plain,
    ( ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl17_17
    | ~ spl17_20
    | spl17_22
    | ~ spl17_47 ),
    inference(subsumption_resolution,[],[f2368,f1906])).

fof(f1906,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ spl17_17 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f1905,plain,
    ( spl17_17
  <=> m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_17])])).

fof(f2368,plain,
    ( ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl17_20
    | spl17_22
    | ~ spl17_47 ),
    inference(subsumption_resolution,[],[f2367,f1945])).

fof(f1945,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl17_20 ),
    inference(avatar_component_clause,[],[f1944])).

fof(f1944,plain,
    ( spl17_20
  <=> m1_subset_1(k2_mcart_1(sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).

fof(f2367,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl17_22
    | ~ spl17_47 ),
    inference(subsumption_resolution,[],[f2365,f1953])).

fof(f1953,plain,
    ( sK4 != k2_mcart_1(sK5)
    | spl17_22 ),
    inference(avatar_component_clause,[],[f1952])).

fof(f1952,plain,
    ( spl17_22
  <=> sK4 = k2_mcart_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_22])])).

fof(f2365,plain,
    ( sK4 = k2_mcart_1(sK5)
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl17_47 ),
    inference(trivial_inequality_removal,[],[f2339])).

fof(f2339,plain,
    ( sK5 != sK5
    | sK4 = k2_mcart_1(sK5)
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl17_47 ),
    inference(superposition,[],[f1438,f2318])).

fof(f2318,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(sK5))
    | ~ spl17_47 ),
    inference(avatar_component_clause,[],[f2317])).

fof(f2317,plain,
    ( spl17_47
  <=> sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_47])])).

fof(f1438,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X9
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f1419])).

fof(f1419,plain,
    ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1396,f1418])).

fof(f1418,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X9
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f1396,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f1395])).

fof(f1395,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1392])).

fof(f1392,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1391])).

fof(f1391,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

fof(f2319,plain,
    ( spl17_47
    | ~ spl17_33
    | ~ spl17_35 ),
    inference(avatar_split_clause,[],[f2315,f2168,f2121,f2317])).

fof(f2315,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(sK5))
    | ~ spl17_33
    | ~ spl17_35 ),
    inference(forward_demodulation,[],[f2122,f2169])).

fof(f2169,plain,
    ( sK14(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | ~ spl17_35 ),
    inference(avatar_component_clause,[],[f2168])).

fof(f2123,plain,
    ( spl17_33
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f2119,f1546,f1542,f1538,f1534,f1530,f2121])).

fof(f1530,plain,
    ( spl17_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f1534,plain,
    ( spl17_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f1538,plain,
    ( spl17_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f1542,plain,
    ( spl17_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).

fof(f1546,plain,
    ( spl17_6
  <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f2119,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2118,f1543])).

fof(f1543,plain,
    ( k1_xboole_0 != sK0
    | spl17_5 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f2118,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2117,f1539])).

fof(f1539,plain,
    ( k1_xboole_0 != sK1
    | spl17_4 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f2117,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2116,f1535])).

fof(f1535,plain,
    ( k1_xboole_0 != sK2
    | spl17_3 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f2116,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2109,f1531])).

fof(f1531,plain,
    ( k1_xboole_0 != sK3
    | spl17_2 ),
    inference(avatar_component_clause,[],[f1530])).

fof(f2109,plain,
    ( sK5 = k4_mcart_1(sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5),sK14(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1476,f1547])).

fof(f1547,plain,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f1476,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4),sK14(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4),sK14(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK14(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK13(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK12(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK11(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13,sK14])],[f1408,f1429,f1428,f1427,f1426])).

fof(f1426,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK11(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1427,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK12(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1428,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK13(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f1429,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4),sK14(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK14(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f1408,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1300])).

fof(f1300,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f2079,plain,
    ( spl17_29
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_19
    | ~ spl17_23
    | ~ spl17_24
    | ~ spl17_25 ),
    inference(avatar_split_clause,[],[f2075,f2000,f1984,f1968,f1937,f1546,f1542,f1538,f1534,f1530,f2077])).

fof(f1937,plain,
    ( spl17_19
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f1968,plain,
    ( spl17_23
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_23])])).

fof(f1984,plain,
    ( spl17_24
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).

fof(f2000,plain,
    ( spl17_25
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_25])])).

fof(f2075,plain,
    ( sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_19
    | ~ spl17_23
    | ~ spl17_24
    | ~ spl17_25 ),
    inference(forward_demodulation,[],[f2074,f1985])).

fof(f1985,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | ~ spl17_24 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f2074,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_19
    | ~ spl17_23
    | ~ spl17_25 ),
    inference(forward_demodulation,[],[f2073,f2001])).

fof(f2001,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | ~ spl17_25 ),
    inference(avatar_component_clause,[],[f2000])).

fof(f2073,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_19
    | ~ spl17_23 ),
    inference(forward_demodulation,[],[f2072,f1969])).

fof(f1969,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | ~ spl17_23 ),
    inference(avatar_component_clause,[],[f1968])).

fof(f2072,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_19 ),
    inference(forward_demodulation,[],[f2071,f1938])).

fof(f1938,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f1937])).

fof(f2071,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2070,f1543])).

fof(f2070,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2069,f1539])).

fof(f2069,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2068,f1535])).

fof(f2068,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f2061,f1531])).

fof(f2061,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1464,f1547])).

fof(f1464,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1404])).

fof(f1404,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1367])).

fof(f1367,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f2002,plain,
    ( spl17_25
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1998,f1546,f1542,f1538,f1534,f1530,f2000])).

fof(f1998,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1997,f1543])).

fof(f1997,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1996,f1539])).

fof(f1996,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1995,f1535])).

fof(f1995,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1988,f1531])).

fof(f1988,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1457,f1547])).

fof(f1457,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1402])).

fof(f1402,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1368])).

fof(f1368,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f1986,plain,
    ( spl17_24
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1982,f1546,f1542,f1538,f1534,f1530,f1984])).

fof(f1982,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1981,f1543])).

fof(f1981,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1980,f1539])).

fof(f1980,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1979,f1535])).

fof(f1979,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1972,f1531])).

fof(f1972,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1456,f1547])).

fof(f1456,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1402])).

fof(f1970,plain,
    ( spl17_23
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1966,f1546,f1542,f1538,f1534,f1530,f1968])).

fof(f1966,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1965,f1543])).

fof(f1965,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1964,f1539])).

fof(f1964,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1963,f1535])).

fof(f1963,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1956,f1531])).

fof(f1956,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1458,f1547])).

fof(f1458,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1402])).

fof(f1954,plain,
    ( ~ spl17_22
    | spl17_1
    | ~ spl17_19 ),
    inference(avatar_split_clause,[],[f1942,f1937,f1526,f1952])).

fof(f1526,plain,
    ( spl17_1
  <=> sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f1942,plain,
    ( sK4 != k2_mcart_1(sK5)
    | spl17_1
    | ~ spl17_19 ),
    inference(superposition,[],[f1527,f1938])).

fof(f1527,plain,
    ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | spl17_1 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1946,plain,
    ( spl17_20
    | ~ spl17_10
    | ~ spl17_19 ),
    inference(avatar_split_clause,[],[f1940,f1937,f1653,f1944])).

fof(f1653,plain,
    ( spl17_10
  <=> m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f1940,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl17_10
    | ~ spl17_19 ),
    inference(backward_demodulation,[],[f1654,f1938])).

fof(f1654,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f1653])).

fof(f1939,plain,
    ( spl17_19
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1935,f1546,f1542,f1538,f1534,f1530,f1937])).

fof(f1935,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1934,f1543])).

fof(f1934,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1933,f1539])).

fof(f1933,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1932,f1535])).

fof(f1932,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1925,f1531])).

fof(f1925,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1459,f1547])).

fof(f1459,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1402])).

fof(f1907,plain,
    ( spl17_17
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1903,f1546,f1542,f1538,f1534,f1530,f1905])).

fof(f1903,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1902,f1543])).

fof(f1902,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1901,f1539])).

fof(f1901,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1900,f1535])).

fof(f1900,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1893,f1531])).

fof(f1893,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1474,f1547])).

fof(f1474,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK13(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1891,plain,
    ( spl17_16
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1887,f1546,f1542,f1538,f1534,f1530,f1889])).

fof(f1887,plain,
    ( m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1886,f1543])).

fof(f1886,plain,
    ( m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1885,f1539])).

fof(f1885,plain,
    ( m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1884,f1535])).

fof(f1884,plain,
    ( m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1877,f1531])).

fof(f1877,plain,
    ( m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1473,f1547])).

fof(f1473,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK12(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1875,plain,
    ( spl17_15
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1871,f1546,f1542,f1538,f1534,f1530,f1873])).

fof(f1871,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl17_2
    | spl17_3
    | spl17_4
    | spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1870,f1543])).

fof(f1870,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1869,f1539])).

fof(f1869,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | spl17_3
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1868,f1535])).

fof(f1868,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl17_2
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1861,f1531])).

fof(f1861,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl17_6 ),
    inference(resolution,[],[f1472,f1547])).

fof(f1472,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK11(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1655,plain,
    ( spl17_10
    | ~ spl17_6 ),
    inference(avatar_split_clause,[],[f1645,f1546,f1653])).

fof(f1645,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl17_6 ),
    inference(resolution,[],[f1448,f1547])).

fof(f1448,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f1548,plain,(
    spl17_6 ),
    inference(avatar_split_clause,[],[f1437,f1546])).

fof(f1437,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f1419])).

fof(f1544,plain,(
    ~ spl17_5 ),
    inference(avatar_split_clause,[],[f1439,f1542])).

fof(f1439,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1419])).

fof(f1540,plain,(
    ~ spl17_4 ),
    inference(avatar_split_clause,[],[f1440,f1538])).

fof(f1440,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1419])).

fof(f1536,plain,(
    ~ spl17_3 ),
    inference(avatar_split_clause,[],[f1441,f1534])).

fof(f1441,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1419])).

fof(f1532,plain,(
    ~ spl17_2 ),
    inference(avatar_split_clause,[],[f1442,f1530])).

fof(f1442,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1419])).

fof(f1528,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f1443,f1526])).

fof(f1443,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f1419])).
%------------------------------------------------------------------------------
