%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0868+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 309 expanded)
%              Number of equality atoms :   77 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1483,f1487,f1491,f1495,f2364,f2368,f2378])).

fof(f2378,plain,
    ( ~ spl10_1
    | ~ spl10_19 ),
    inference(avatar_contradiction_clause,[],[f2377])).

fof(f2377,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f2376,f1534])).

fof(f1534,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X1 ),
    inference(forward_demodulation,[],[f1469,f1411])).

fof(f1411,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1314])).

fof(f1314,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1469,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f1416])).

fof(f1416,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f1335])).

fof(f1335,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1303])).

fof(f1303,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f2376,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl10_1
    | ~ spl10_19 ),
    inference(forward_demodulation,[],[f2367,f1479])).

fof(f1479,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f1478])).

fof(f1478,plain,
    ( spl10_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f2367,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f2366])).

fof(f2366,plain,
    ( spl10_19
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f2368,plain,
    ( spl10_19
    | ~ spl10_3
    | spl10_4
    | spl10_5 ),
    inference(avatar_split_clause,[],[f2361,f1493,f1489,f1485,f2366])).

fof(f1485,plain,
    ( spl10_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1489,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f1493,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f2361,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl10_3
    | spl10_4
    | spl10_5 ),
    inference(subsumption_resolution,[],[f2360,f1494])).

fof(f1494,plain,
    ( k1_xboole_0 != sK0
    | spl10_5 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f2360,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | k1_xboole_0 = sK0
    | ~ spl10_3
    | spl10_4 ),
    inference(subsumption_resolution,[],[f2355,f1490])).

fof(f1490,plain,
    ( k1_xboole_0 != sK1
    | spl10_4 ),
    inference(avatar_component_clause,[],[f1489])).

fof(f2355,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_3 ),
    inference(resolution,[],[f1409,f1486])).

fof(f1486,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f1485])).

fof(f1409,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1331])).

fof(f1331,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1305])).

fof(f1305,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f2364,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | spl10_5 ),
    inference(avatar_contradiction_clause,[],[f2363])).

fof(f2363,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | spl10_5 ),
    inference(subsumption_resolution,[],[f2362,f1533])).

fof(f1533,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f1468,f1412])).

fof(f1412,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1314])).

fof(f1468,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f1417])).

fof(f1417,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f1335])).

fof(f2362,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | spl10_5 ),
    inference(forward_demodulation,[],[f2361,f1482])).

fof(f1482,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1481,plain,
    ( spl10_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1495,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f1386,f1493])).

fof(f1386,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1369])).

fof(f1369,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1319,f1368,f1367])).

fof(f1367,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f1368,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f1319,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1308])).

fof(f1308,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1307])).

fof(f1307,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f1491,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f1387,f1489])).

fof(f1387,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1369])).

fof(f1487,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f1388,f1485])).

fof(f1388,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1483,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f1389,f1481,f1478])).

fof(f1389,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f1369])).
%------------------------------------------------------------------------------
