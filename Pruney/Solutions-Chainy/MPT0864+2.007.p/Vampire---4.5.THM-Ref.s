%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 162 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  215 ( 416 expanded)
%              Number of equality atoms :   98 ( 222 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1075,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f907,f913,f919,f934,f1068,f1074])).

fof(f1074,plain,(
    ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f66,f1067])).

fof(f1067,plain,
    ( ! [X3] : ~ r2_hidden(sK1,X3)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1066,plain,
    ( spl10_13
  <=> ! [X3] : ~ r2_hidden(sK1,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f66,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1068,plain,
    ( spl10_13
    | ~ spl10_6
    | spl10_7
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f1061,f76,f904,f900,f1066])).

fof(f900,plain,
    ( spl10_6
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f904,plain,
    ( spl10_7
  <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f76,plain,
    ( spl10_1
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1061,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
        | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
        | ~ r2_hidden(sK1,X3) )
    | ~ spl10_1 ),
    inference(resolution,[],[f877,f974])).

fof(f974,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK0,X1)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f176,f944])).

fof(f944,plain,
    ( sK0 = sK2
    | ~ spl10_1 ),
    inference(superposition,[],[f78,f87])).

fof(f87,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f29,f20])).

fof(f20,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f78,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f176,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f71,f20])).

fof(f71,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f877,plain,(
    ! [X37,X36] :
      ( ~ r2_hidden(X36,k2_zfmisc_1(X37,k1_enumset1(X36,X36,X36)))
      | k1_xboole_0 = k1_enumset1(X36,X36,X36) ) ),
    inference(duplicate_literal_removal,[],[f872])).

fof(f872,plain,(
    ! [X37,X36] :
      ( ~ r2_hidden(X36,k2_zfmisc_1(X37,k1_enumset1(X36,X36,X36)))
      | k1_xboole_0 = k1_enumset1(X36,X36,X36)
      | k1_xboole_0 = k1_enumset1(X36,X36,X36) ) ),
    inference(superposition,[],[f812,f858])).

fof(f858,plain,(
    ! [X0] :
      ( sK3(k1_enumset1(X0,X0,X0)) = X0
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(equality_resolution,[],[f841])).

fof(f841,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | sK3(k1_enumset1(X0,X0,X1)) = X1
      | k1_xboole_0 = k1_enumset1(X0,X0,X1) ) ),
    inference(equality_factoring,[],[f148])).

fof(f148,plain,(
    ! [X4,X5] :
      ( sK3(k1_enumset1(X5,X5,X4)) = X5
      | sK3(k1_enumset1(X5,X5,X4)) = X4
      | k1_xboole_0 = k1_enumset1(X5,X5,X4) ) ),
    inference(resolution,[],[f69,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f27])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f812,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f809])).

fof(f809,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(sK3(X0),k2_zfmisc_1(X1,X0))
      | ~ r2_hidden(sK3(X0),k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f808,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f808,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,sK3(X2)),X2)
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK3(X2),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f199])).

fof(f199,plain,(
    ! [X12,X10,X13,X11] :
      ( sK3(X13) != X12
      | ~ r2_hidden(sK7(X10,X11,X12),X13)
      | k1_xboole_0 = X13
      | ~ r2_hidden(X12,k2_zfmisc_1(X10,X11)) ) ),
    inference(superposition,[],[f24,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f934,plain,(
    ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f920])).

fof(f920,plain,
    ( $false
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f93,f906])).

fof(f906,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f904])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f54,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f26,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f919,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f914])).

fof(f914,plain,
    ( $false
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f66,f898])).

fof(f898,plain,
    ( ! [X3] : ~ r2_hidden(sK2,X3)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl10_5
  <=> ! [X3] : ~ r2_hidden(sK2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f913,plain,(
    spl10_6 ),
    inference(avatar_contradiction_clause,[],[f908])).

fof(f908,plain,
    ( $false
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f66,f902])).

fof(f902,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f900])).

fof(f907,plain,
    ( spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f892,f80,f904,f900,f897])).

fof(f80,plain,
    ( spl10_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f892,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
        | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
        | ~ r2_hidden(sK2,X3) )
    | ~ spl10_2 ),
    inference(resolution,[],[f875,f182])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(sK2,X1) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f176,f85])).

fof(f85,plain,
    ( sK0 = sK1
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f84,f82])).

fof(f82,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f84,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f28,f20])).

fof(f28,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f875,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,k2_zfmisc_1(k1_enumset1(X41,X41,X41),X42))
      | k1_xboole_0 = k1_enumset1(X41,X41,X41) ) ),
    inference(duplicate_literal_removal,[],[f874])).

fof(f874,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,k2_zfmisc_1(k1_enumset1(X41,X41,X41),X42))
      | k1_xboole_0 = k1_enumset1(X41,X41,X41)
      | k1_xboole_0 = k1_enumset1(X41,X41,X41) ) ),
    inference(superposition,[],[f822,f858])).

fof(f822,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f819])).

fof(f819,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(sK3(X0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK3(X0),k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f818,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f818,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK3(X2)),X2)
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK3(X2),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f200])).

fof(f200,plain,(
    ! [X14,X17,X15,X16] :
      ( sK3(X17) != X16
      | ~ r2_hidden(sK6(X14,X15,X16),X17)
      | k1_xboole_0 = X17
      | ~ r2_hidden(X16,k2_zfmisc_1(X14,X15)) ) ),
    inference(superposition,[],[f23,f72])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f19,f80,f76])).

fof(f19,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:08 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.46  % (27691)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.47  % (27683)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (27699)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (27688)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (27681)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (27688)Refutation not found, incomplete strategy% (27688)------------------------------
% 0.20/0.50  % (27688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27680)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (27688)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27688)Memory used [KB]: 10746
% 0.20/0.51  % (27688)Time elapsed: 0.094 s
% 0.20/0.51  % (27688)------------------------------
% 0.20/0.51  % (27688)------------------------------
% 0.20/0.51  % (27702)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (27705)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (27689)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (27703)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (27691)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1075,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f83,f907,f913,f919,f934,f1068,f1074])).
% 0.20/0.52  fof(f1074,plain,(
% 0.20/0.52    ~spl10_13),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f1069])).
% 0.20/0.52  fof(f1069,plain,(
% 0.20/0.52    $false | ~spl10_13),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f66,f1067])).
% 0.20/0.52  fof(f1067,plain,(
% 0.20/0.52    ( ! [X3] : (~r2_hidden(sK1,X3)) ) | ~spl10_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f1066])).
% 0.20/0.52  fof(f1066,plain,(
% 0.20/0.52    spl10_13 <=> ! [X3] : ~r2_hidden(sK1,X3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 0.20/0.52    inference(equality_resolution,[],[f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 0.20/0.52    inference(equality_resolution,[],[f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f44,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.52  fof(f1068,plain,(
% 0.20/0.52    spl10_13 | ~spl10_6 | spl10_7 | ~spl10_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f1061,f76,f904,f900,f1066])).
% 0.20/0.52  fof(f900,plain,(
% 0.20/0.52    spl10_6 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.52  fof(f904,plain,(
% 0.20/0.52    spl10_7 <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl10_1 <=> sK0 = k2_mcart_1(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.52  fof(f1061,plain,(
% 0.20/0.52    ( ! [X3] : (k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK1,X3)) ) | ~spl10_1),
% 0.20/0.52    inference(resolution,[],[f877,f974])).
% 0.20/0.52  fof(f974,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X1) | ~r2_hidden(sK1,X0)) ) | ~spl10_1),
% 0.20/0.52    inference(forward_demodulation,[],[f176,f944])).
% 0.20/0.52  fof(f944,plain,(
% 0.20/0.52    sK0 = sK2 | ~spl10_1),
% 0.20/0.52    inference(superposition,[],[f78,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    sK2 = k2_mcart_1(sK0)),
% 0.20/0.52    inference(superposition,[],[f29,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    sK0 = k4_tarski(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    sK0 = k2_mcart_1(sK0) | ~spl10_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f76])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK2,X1) | ~r2_hidden(sK1,X0)) )),
% 0.20/0.52    inference(superposition,[],[f71,f20])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(equality_resolution,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.52  fof(f877,plain,(
% 0.20/0.52    ( ! [X37,X36] : (~r2_hidden(X36,k2_zfmisc_1(X37,k1_enumset1(X36,X36,X36))) | k1_xboole_0 = k1_enumset1(X36,X36,X36)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f872])).
% 0.20/0.52  fof(f872,plain,(
% 0.20/0.52    ( ! [X37,X36] : (~r2_hidden(X36,k2_zfmisc_1(X37,k1_enumset1(X36,X36,X36))) | k1_xboole_0 = k1_enumset1(X36,X36,X36) | k1_xboole_0 = k1_enumset1(X36,X36,X36)) )),
% 0.20/0.52    inference(superposition,[],[f812,f858])).
% 0.20/0.52  fof(f858,plain,(
% 0.20/0.52    ( ! [X0] : (sK3(k1_enumset1(X0,X0,X0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f841])).
% 0.20/0.52  fof(f841,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 != X1 | sK3(k1_enumset1(X0,X0,X1)) = X1 | k1_xboole_0 = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(equality_factoring,[],[f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X4,X5] : (sK3(k1_enumset1(X5,X5,X4)) = X5 | sK3(k1_enumset1(X5,X5,X4)) = X4 | k1_xboole_0 = k1_enumset1(X5,X5,X4)) )),
% 0.20/0.52    inference(resolution,[],[f69,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.20/0.52    inference(equality_resolution,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f42,f27])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f812,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f809])).
% 0.20/0.52  fof(f809,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK3(X0),k2_zfmisc_1(X1,X0)) | ~r2_hidden(sK3(X0),k2_zfmisc_1(X1,X0))) )),
% 0.20/0.52    inference(resolution,[],[f808,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f808,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,sK3(X2)),X2) | k1_xboole_0 = X2 | ~r2_hidden(sK3(X2),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f199])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ( ! [X12,X10,X13,X11] : (sK3(X13) != X12 | ~r2_hidden(sK7(X10,X11,X12),X13) | k1_xboole_0 = X13 | ~r2_hidden(X12,k2_zfmisc_1(X10,X11))) )),
% 0.20/0.52    inference(superposition,[],[f24,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f934,plain,(
% 0.20/0.52    ~spl10_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f920])).
% 0.20/0.52  fof(f920,plain,(
% 0.20/0.52    $false | ~spl10_7),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f93,f906])).
% 0.20/0.52  fof(f906,plain,(
% 0.20/0.52    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl10_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f904])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.20/0.52    inference(superposition,[],[f54,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f26,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f22,f27])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.52  fof(f919,plain,(
% 0.20/0.52    ~spl10_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f914])).
% 0.20/0.52  fof(f914,plain,(
% 0.20/0.52    $false | ~spl10_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f66,f898])).
% 0.20/0.52  fof(f898,plain,(
% 0.20/0.52    ( ! [X3] : (~r2_hidden(sK2,X3)) ) | ~spl10_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f897])).
% 0.20/0.52  fof(f897,plain,(
% 0.20/0.52    spl10_5 <=> ! [X3] : ~r2_hidden(sK2,X3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.52  fof(f913,plain,(
% 0.20/0.52    spl10_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f908])).
% 0.20/0.52  fof(f908,plain,(
% 0.20/0.52    $false | spl10_6),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f66,f902])).
% 0.20/0.52  fof(f902,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl10_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f900])).
% 0.20/0.52  fof(f907,plain,(
% 0.20/0.52    spl10_5 | ~spl10_6 | spl10_7 | ~spl10_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f892,f80,f904,f900,f897])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    spl10_2 <=> sK0 = k1_mcart_1(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.52  fof(f892,plain,(
% 0.20/0.52    ( ! [X3] : (k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2,X3)) ) | ~spl10_2),
% 0.20/0.52    inference(resolution,[],[f875,f182])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X0) | ~r2_hidden(sK2,X1)) ) | ~spl10_2),
% 0.20/0.52    inference(forward_demodulation,[],[f176,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    sK0 = sK1 | ~spl10_2),
% 0.20/0.52    inference(forward_demodulation,[],[f84,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    sK0 = k1_mcart_1(sK0) | ~spl10_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f80])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    sK1 = k1_mcart_1(sK0)),
% 0.20/0.52    inference(superposition,[],[f28,f20])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f875,plain,(
% 0.20/0.52    ( ! [X41,X42] : (~r2_hidden(X41,k2_zfmisc_1(k1_enumset1(X41,X41,X41),X42)) | k1_xboole_0 = k1_enumset1(X41,X41,X41)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f874])).
% 0.20/0.52  fof(f874,plain,(
% 0.20/0.52    ( ! [X41,X42] : (~r2_hidden(X41,k2_zfmisc_1(k1_enumset1(X41,X41,X41),X42)) | k1_xboole_0 = k1_enumset1(X41,X41,X41) | k1_xboole_0 = k1_enumset1(X41,X41,X41)) )),
% 0.20/0.52    inference(superposition,[],[f822,f858])).
% 0.20/0.52  fof(f822,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f819])).
% 0.20/0.52  fof(f819,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK3(X0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK3(X0),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f818,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f818,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,sK3(X2)),X2) | k1_xboole_0 = X2 | ~r2_hidden(sK3(X2),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f200])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    ( ! [X14,X17,X15,X16] : (sK3(X17) != X16 | ~r2_hidden(sK6(X14,X15,X16),X17) | k1_xboole_0 = X17 | ~r2_hidden(X16,k2_zfmisc_1(X14,X15))) )),
% 0.20/0.52    inference(superposition,[],[f23,f72])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl10_1 | spl10_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f19,f80,f76])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (27691)------------------------------
% 0.20/0.52  % (27691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27691)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (27691)Memory used [KB]: 6908
% 0.20/0.52  % (27691)Time elapsed: 0.117 s
% 0.20/0.52  % (27691)------------------------------
% 0.20/0.52  % (27691)------------------------------
% 0.20/0.52  % (27678)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (27677)Success in time 0.164 s
%------------------------------------------------------------------------------
