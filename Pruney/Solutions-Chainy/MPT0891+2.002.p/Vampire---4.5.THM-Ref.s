%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:06 EST 2020

% Result     : Theorem 4.41s
% Output     : Refutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 331 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  461 ( 924 expanded)
%              Number of equality atoms :  189 ( 443 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f363,f368,f373,f378,f391,f455,f525,f650,f796,f804,f835,f1098,f3334,f3397])).

fof(f3397,plain,(
    ~ spl35_19 ),
    inference(avatar_contradiction_clause,[],[f3396])).

fof(f3396,plain,
    ( $false
    | ~ spl35_19 ),
    inference(subsumption_resolution,[],[f3386,f330])).

fof(f330,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3386,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | ~ spl35_19 ),
    inference(superposition,[],[f1715,f649])).

fof(f649,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ spl35_19 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl35_19
  <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_19])])).

fof(f1715,plain,(
    ! [X4,X5,X3] : ~ r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X3,X4,X5))) ),
    inference(subsumption_resolution,[],[f1710,f1134])).

fof(f1134,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f209,f167])).

fof(f167,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f209,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1710,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X3,X4,X5)))
      | k1_xboole_0 = k1_tarski(X5) ) ),
    inference(superposition,[],[f275,f270])).

fof(f270,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f136])).

fof(f136,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f3334,plain,(
    ~ spl35_23 ),
    inference(avatar_contradiction_clause,[],[f3333])).

fof(f3333,plain,
    ( $false
    | ~ spl35_23 ),
    inference(subsumption_resolution,[],[f3324,f330])).

fof(f3324,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | ~ spl35_23 ),
    inference(superposition,[],[f1716,f834])).

fof(f834,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl35_23 ),
    inference(avatar_component_clause,[],[f832])).

fof(f832,plain,
    ( spl35_23
  <=> sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_23])])).

fof(f1716,plain,(
    ! [X6,X8,X7] : ~ r1_tarski(k1_tarski(X6),k1_tarski(k3_mcart_1(X6,X7,X8))) ),
    inference(subsumption_resolution,[],[f1711,f1134])).

fof(f1711,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k1_tarski(X6),k1_tarski(k3_mcart_1(X6,X7,X8)))
      | k1_xboole_0 = k1_tarski(X6) ) ),
    inference(superposition,[],[f274,f270])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f136])).

fof(f1098,plain,(
    ~ spl35_20 ),
    inference(avatar_contradiction_clause,[],[f1097])).

fof(f1097,plain,
    ( $false
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f1005,f1080])).

fof(f1080,plain,
    ( ! [X2] : ~ v1_xboole_0(X2)
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f1079,f1061])).

fof(f1061,plain,
    ( ! [X2,X0] : r2_hidden(X0,X2)
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f879,f1032])).

fof(f1032,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f183,f1030])).

fof(f1030,plain,
    ( ! [X0,X1] : r1_tarski(X0,X1)
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f877,f858])).

fof(f858,plain,
    ( ! [X1] : sK3 = X1
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f842,f337])).

fof(f337,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f246])).

fof(f246,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f842,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X1))
        | sK3 = X1 )
    | ~ spl35_20 ),
    inference(superposition,[],[f229,f795])).

fof(f795,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl35_20 ),
    inference(avatar_component_clause,[],[f793])).

fof(f793,plain,
    ( spl35_20
  <=> k1_xboole_0 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_20])])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f877,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != sK3
        | r1_tarski(X0,X1) )
    | ~ spl35_20 ),
    inference(backward_demodulation,[],[f251,f858])).

fof(f251,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f879,plain,
    ( ! [X2,X0] :
        ( k1_xboole_0 != sK3
        | r2_hidden(X0,X2) )
    | ~ spl35_20 ),
    inference(backward_demodulation,[],[f289,f858])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f1079,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f929,f1063])).

fof(f1063,plain,
    ( ! [X0,X1] : m1_subset_1(X0,X1)
    | ~ spl35_20 ),
    inference(subsumption_resolution,[],[f220,f1061])).

fof(f220,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f929,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,sK3)
        | ~ v1_xboole_0(X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl35_20 ),
    inference(backward_demodulation,[],[f313,f858])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f1005,plain,
    ( v1_xboole_0(sK3)
    | ~ spl35_20 ),
    inference(backward_demodulation,[],[f207,f858])).

fof(f207,plain,(
    ! [X0] : v1_xboole_0(sK12(X0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f835,plain,
    ( spl35_23
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_7 ),
    inference(avatar_split_clause,[],[f818,f388,f375,f370,f365,f360,f832])).

fof(f360,plain,
    ( spl35_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_1])])).

fof(f365,plain,
    ( spl35_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_2])])).

fof(f370,plain,
    ( spl35_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_3])])).

fof(f375,plain,
    ( spl35_4
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_4])])).

fof(f388,plain,
    ( spl35_7
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_7])])).

fof(f818,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_7 ),
    inference(subsumption_resolution,[],[f817,f362])).

fof(f362,plain,
    ( k1_xboole_0 != sK0
    | spl35_1 ),
    inference(avatar_component_clause,[],[f360])).

fof(f817,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_7 ),
    inference(subsumption_resolution,[],[f816,f377])).

fof(f377,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl35_4 ),
    inference(avatar_component_clause,[],[f375])).

fof(f816,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_7 ),
    inference(subsumption_resolution,[],[f815,f372])).

fof(f372,plain,
    ( k1_xboole_0 != sK2
    | spl35_3 ),
    inference(avatar_component_clause,[],[f370])).

fof(f815,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | ~ spl35_7 ),
    inference(subsumption_resolution,[],[f814,f367])).

fof(f367,plain,
    ( k1_xboole_0 != sK1
    | spl35_2 ),
    inference(avatar_component_clause,[],[f365])).

fof(f814,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ spl35_7 ),
    inference(superposition,[],[f296,f390])).

fof(f390,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl35_7 ),
    inference(avatar_component_clause,[],[f388])).

fof(f296,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f804,plain,
    ( spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_14
    | spl35_18 ),
    inference(avatar_contradiction_clause,[],[f803])).

fof(f803,plain,
    ( $false
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_14
    | spl35_18 ),
    inference(subsumption_resolution,[],[f631,f802])).

fof(f802,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_14 ),
    inference(subsumption_resolution,[],[f801,f362])).

fof(f801,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_14 ),
    inference(subsumption_resolution,[],[f800,f377])).

fof(f800,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_14 ),
    inference(subsumption_resolution,[],[f799,f372])).

fof(f799,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | ~ spl35_14 ),
    inference(subsumption_resolution,[],[f689,f367])).

fof(f689,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ spl35_14 ),
    inference(superposition,[],[f524,f299])).

fof(f299,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f524,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl35_14 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl35_14
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_14])])).

fof(f631,plain,
    ( sK3 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | spl35_18 ),
    inference(avatar_component_clause,[],[f630])).

fof(f630,plain,
    ( spl35_18
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_18])])).

fof(f796,plain,
    ( spl35_20
    | ~ spl35_18 ),
    inference(avatar_split_clause,[],[f741,f630,f793])).

fof(f741,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl35_18 ),
    inference(subsumption_resolution,[],[f731,f348])).

fof(f348,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f286])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f731,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_tarski(sK3),k2_tarski(sK3,k3_mcart_1(X2,sK3,k2_mcart_1(sK3))))
        | k1_xboole_0 = k1_tarski(sK3) )
    | ~ spl35_18 ),
    inference(superposition,[],[f276,f674])).

fof(f674,plain,
    ( ! [X4] : k2_tarski(sK3,k3_mcart_1(X4,sK3,k2_mcart_1(sK3))) = k3_zfmisc_1(k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),X4),k1_tarski(sK3),k1_tarski(k2_mcart_1(sK3)))
    | ~ spl35_18 ),
    inference(superposition,[],[f317,f632])).

fof(f632,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | ~ spl35_18 ),
    inference(avatar_component_clause,[],[f630])).

fof(f317,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f136])).

fof(f650,plain,
    ( spl35_19
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_5 ),
    inference(avatar_split_clause,[],[f644,f380,f375,f370,f365,f360,f647])).

fof(f380,plain,
    ( spl35_5
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_5])])).

fof(f644,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_5 ),
    inference(subsumption_resolution,[],[f643,f362])).

fof(f643,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_5 ),
    inference(subsumption_resolution,[],[f642,f377])).

fof(f642,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_5 ),
    inference(subsumption_resolution,[],[f641,f372])).

fof(f641,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | ~ spl35_5 ),
    inference(subsumption_resolution,[],[f640,f367])).

fof(f640,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ spl35_5 ),
    inference(superposition,[],[f296,f382])).

fof(f382,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl35_5 ),
    inference(avatar_component_clause,[],[f380])).

fof(f525,plain,
    ( spl35_14
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_12 ),
    inference(avatar_split_clause,[],[f470,f452,f375,f370,f365,f360,f522])).

fof(f452,plain,
    ( spl35_12
  <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_12])])).

fof(f470,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_12 ),
    inference(subsumption_resolution,[],[f469,f362])).

fof(f469,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_12 ),
    inference(subsumption_resolution,[],[f468,f377])).

fof(f468,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_12 ),
    inference(subsumption_resolution,[],[f467,f372])).

fof(f467,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | ~ spl35_12 ),
    inference(subsumption_resolution,[],[f456,f367])).

fof(f456,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ spl35_12 ),
    inference(superposition,[],[f454,f297])).

fof(f297,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f139])).

fof(f454,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl35_12 ),
    inference(avatar_component_clause,[],[f452])).

fof(f455,plain,
    ( spl35_12
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_6 ),
    inference(avatar_split_clause,[],[f450,f384,f375,f370,f365,f360,f452])).

fof(f384,plain,
    ( spl35_6
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_6])])).

fof(f450,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl35_1
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_6 ),
    inference(subsumption_resolution,[],[f449,f362])).

fof(f449,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_4
    | ~ spl35_6 ),
    inference(subsumption_resolution,[],[f448,f377])).

fof(f448,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | spl35_3
    | ~ spl35_6 ),
    inference(subsumption_resolution,[],[f447,f372])).

fof(f447,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl35_2
    | ~ spl35_6 ),
    inference(subsumption_resolution,[],[f446,f367])).

fof(f446,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ spl35_6 ),
    inference(superposition,[],[f296,f386])).

fof(f386,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl35_6 ),
    inference(avatar_component_clause,[],[f384])).

fof(f391,plain,
    ( spl35_5
    | spl35_6
    | spl35_7 ),
    inference(avatar_split_clause,[],[f151,f388,f384,f380])).

fof(f151,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f89])).

fof(f89,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f88])).

fof(f88,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f378,plain,(
    spl35_4 ),
    inference(avatar_split_clause,[],[f152,f375])).

fof(f152,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f91])).

fof(f373,plain,(
    ~ spl35_3 ),
    inference(avatar_split_clause,[],[f155,f370])).

fof(f155,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f91])).

fof(f368,plain,(
    ~ spl35_2 ),
    inference(avatar_split_clause,[],[f154,f365])).

fof(f154,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f91])).

fof(f363,plain,(
    ~ spl35_1 ),
    inference(avatar_split_clause,[],[f153,f360])).

fof(f153,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (1532)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1530)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (1537)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (1514)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.57  % (1516)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.57  % (1536)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.57  % (1522)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.57  % (1524)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.58  % (1508)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.58  % (1529)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.61/0.58  % (1527)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.61/0.59  % (1512)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.61/0.59  % (1521)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.61/0.59  % (1511)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.61/0.59  % (1531)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.61/0.59  % (1518)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.61/0.59  % (1520)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.59  % (1513)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.61/0.59  % (1510)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.59  % (1515)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.59  % (1525)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.61/0.59  % (1517)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.61/0.59  % (1535)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.61/0.60  % (1533)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.61/0.60  % (1528)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.61/0.60  % (1519)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.61/0.60  % (1509)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.61/0.60  % (1534)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.60  % (1526)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.61/0.61  % (1523)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 3.11/0.84  % (1513)Time limit reached!
% 3.11/0.84  % (1513)------------------------------
% 3.11/0.84  % (1513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.11/0.84  % (1513)Termination reason: Time limit
% 3.11/0.84  
% 3.11/0.84  % (1513)Memory used [KB]: 8187
% 3.11/0.84  % (1513)Time elapsed: 0.407 s
% 3.11/0.84  % (1513)------------------------------
% 3.11/0.84  % (1513)------------------------------
% 4.27/0.93  % (1520)Time limit reached!
% 4.27/0.93  % (1520)------------------------------
% 4.27/0.93  % (1520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.93  % (1520)Termination reason: Time limit
% 4.27/0.93  % (1520)Termination phase: Saturation
% 4.27/0.93  
% 4.27/0.93  % (1520)Memory used [KB]: 9210
% 4.27/0.93  % (1520)Time elapsed: 0.502 s
% 4.27/0.93  % (1520)------------------------------
% 4.27/0.93  % (1520)------------------------------
% 4.41/0.95  % (1668)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.41/0.97  % (1508)Time limit reached!
% 4.41/0.97  % (1508)------------------------------
% 4.41/0.97  % (1508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.97  % (1508)Termination reason: Time limit
% 4.41/0.97  % (1508)Termination phase: Saturation
% 4.41/0.97  
% 4.41/0.97  % (1508)Memory used [KB]: 2942
% 4.41/0.97  % (1508)Time elapsed: 0.500 s
% 4.41/0.97  % (1508)------------------------------
% 4.41/0.97  % (1508)------------------------------
% 4.41/0.98  % (1509)Time limit reached!
% 4.41/0.98  % (1509)------------------------------
% 4.41/0.98  % (1509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.98  % (1509)Termination reason: Time limit
% 4.41/0.98  % (1509)Termination phase: Saturation
% 4.41/0.98  
% 4.41/0.98  % (1509)Memory used [KB]: 8443
% 4.41/0.98  % (1509)Time elapsed: 0.508 s
% 4.41/0.98  % (1509)------------------------------
% 4.41/0.98  % (1509)------------------------------
% 4.41/0.98  % (1525)Time limit reached!
% 4.41/0.98  % (1525)------------------------------
% 4.41/0.98  % (1525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.98  % (1525)Termination reason: Time limit
% 4.41/0.98  
% 4.41/0.98  % (1525)Memory used [KB]: 14328
% 4.41/0.98  % (1525)Time elapsed: 0.504 s
% 4.41/0.98  % (1525)------------------------------
% 4.41/0.98  % (1525)------------------------------
% 4.41/1.00  % (1518)Time limit reached!
% 4.41/1.00  % (1518)------------------------------
% 4.41/1.00  % (1518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/1.00  % (1518)Termination reason: Time limit
% 4.41/1.00  
% 4.41/1.00  % (1518)Memory used [KB]: 17782
% 4.41/1.00  % (1518)Time elapsed: 0.545 s
% 4.41/1.00  % (1518)------------------------------
% 4.41/1.00  % (1518)------------------------------
% 4.41/1.01  % (1528)Refutation found. Thanks to Tanya!
% 4.41/1.01  % SZS status Theorem for theBenchmark
% 4.41/1.01  % SZS output start Proof for theBenchmark
% 4.41/1.01  fof(f3398,plain,(
% 4.41/1.01    $false),
% 4.41/1.01    inference(avatar_sat_refutation,[],[f363,f368,f373,f378,f391,f455,f525,f650,f796,f804,f835,f1098,f3334,f3397])).
% 4.41/1.01  fof(f3397,plain,(
% 4.41/1.01    ~spl35_19),
% 4.41/1.01    inference(avatar_contradiction_clause,[],[f3396])).
% 4.41/1.01  fof(f3396,plain,(
% 4.41/1.01    $false | ~spl35_19),
% 4.41/1.01    inference(subsumption_resolution,[],[f3386,f330])).
% 4.41/1.01  fof(f330,plain,(
% 4.41/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.41/1.01    inference(equality_resolution,[],[f234])).
% 4.41/1.01  fof(f234,plain,(
% 4.41/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.41/1.01    inference(cnf_transformation,[],[f6])).
% 4.41/1.01  fof(f6,axiom,(
% 4.41/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.41/1.01  fof(f3386,plain,(
% 4.41/1.01    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | ~spl35_19),
% 4.41/1.01    inference(superposition,[],[f1715,f649])).
% 4.41/1.01  fof(f649,plain,(
% 4.41/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | ~spl35_19),
% 4.41/1.01    inference(avatar_component_clause,[],[f647])).
% 4.41/1.01  fof(f647,plain,(
% 4.41/1.01    spl35_19 <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)),
% 4.41/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_19])])).
% 4.41/1.01  fof(f1715,plain,(
% 4.41/1.01    ( ! [X4,X5,X3] : (~r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X3,X4,X5)))) )),
% 4.41/1.01    inference(subsumption_resolution,[],[f1710,f1134])).
% 4.41/1.01  fof(f1134,plain,(
% 4.41/1.01    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 4.41/1.01    inference(superposition,[],[f209,f167])).
% 4.41/1.01  fof(f167,plain,(
% 4.41/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.41/1.01    inference(cnf_transformation,[],[f10])).
% 4.41/1.01  fof(f10,axiom,(
% 4.41/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 4.41/1.01  fof(f209,plain,(
% 4.41/1.01    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 4.41/1.01    inference(cnf_transformation,[],[f31])).
% 4.41/1.01  fof(f31,axiom,(
% 4.41/1.01    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 4.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 4.41/1.01  fof(f1710,plain,(
% 4.41/1.01    ( ! [X4,X5,X3] : (~r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X3,X4,X5))) | k1_xboole_0 = k1_tarski(X5)) )),
% 4.41/1.01    inference(superposition,[],[f275,f270])).
% 4.41/1.01  fof(f270,plain,(
% 4.41/1.01    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))) )),
% 4.41/1.01    inference(cnf_transformation,[],[f81])).
% 4.41/1.01  fof(f81,axiom,(
% 4.41/1.01    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 4.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
% 4.41/1.01  fof(f275,plain,(
% 4.41/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) | k1_xboole_0 = X0) )),
% 4.41/1.01    inference(cnf_transformation,[],[f136])).
% 4.41/1.01  fof(f136,plain,(
% 4.41/1.01    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 4.41/1.01    inference(ennf_transformation,[],[f86])).
% 4.41/1.01  fof(f86,axiom,(
% 4.41/1.01    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 4.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).
% 4.41/1.01  fof(f3334,plain,(
% 4.41/1.01    ~spl35_23),
% 4.41/1.01    inference(avatar_contradiction_clause,[],[f3333])).
% 4.41/1.01  fof(f3333,plain,(
% 4.41/1.01    $false | ~spl35_23),
% 4.41/1.01    inference(subsumption_resolution,[],[f3324,f330])).
% 4.41/1.01  fof(f3324,plain,(
% 4.41/1.01    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | ~spl35_23),
% 4.41/1.01    inference(superposition,[],[f1716,f834])).
% 4.41/1.01  fof(f834,plain,(
% 4.41/1.01    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl35_23),
% 4.41/1.01    inference(avatar_component_clause,[],[f832])).
% 4.41/1.01  fof(f832,plain,(
% 4.41/1.01    spl35_23 <=> sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 4.41/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_23])])).
% 4.41/1.01  fof(f1716,plain,(
% 4.41/1.01    ( ! [X6,X8,X7] : (~r1_tarski(k1_tarski(X6),k1_tarski(k3_mcart_1(X6,X7,X8)))) )),
% 4.41/1.01    inference(subsumption_resolution,[],[f1711,f1134])).
% 4.41/1.01  fof(f1711,plain,(
% 4.41/1.01    ( ! [X6,X8,X7] : (~r1_tarski(k1_tarski(X6),k1_tarski(k3_mcart_1(X6,X7,X8))) | k1_xboole_0 = k1_tarski(X6)) )),
% 4.41/1.01    inference(superposition,[],[f274,f270])).
% 4.41/1.01  fof(f274,plain,(
% 4.41/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 4.41/1.01    inference(cnf_transformation,[],[f136])).
% 4.41/1.01  fof(f1098,plain,(
% 4.41/1.01    ~spl35_20),
% 4.41/1.01    inference(avatar_contradiction_clause,[],[f1097])).
% 4.41/1.01  fof(f1097,plain,(
% 4.41/1.01    $false | ~spl35_20),
% 4.41/1.01    inference(subsumption_resolution,[],[f1005,f1080])).
% 4.41/1.01  fof(f1080,plain,(
% 4.41/1.01    ( ! [X2] : (~v1_xboole_0(X2)) ) | ~spl35_20),
% 4.41/1.01    inference(subsumption_resolution,[],[f1079,f1061])).
% 4.41/1.01  fof(f1061,plain,(
% 4.41/1.01    ( ! [X2,X0] : (r2_hidden(X0,X2)) ) | ~spl35_20),
% 4.41/1.01    inference(subsumption_resolution,[],[f879,f1032])).
% 4.41/1.01  fof(f1032,plain,(
% 4.41/1.01    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl35_20),
% 4.41/1.01    inference(subsumption_resolution,[],[f183,f1030])).
% 4.41/1.01  fof(f1030,plain,(
% 4.41/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1)) ) | ~spl35_20),
% 4.41/1.01    inference(subsumption_resolution,[],[f877,f858])).
% 4.41/1.01  fof(f858,plain,(
% 4.41/1.01    ( ! [X1] : (sK3 = X1) ) | ~spl35_20),
% 4.41/1.01    inference(subsumption_resolution,[],[f842,f337])).
% 4.41/1.01  fof(f337,plain,(
% 4.41/1.01    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 4.41/1.01    inference(equality_resolution,[],[f246])).
% 4.97/1.01  fof(f246,plain,(
% 4.97/1.01    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 4.97/1.01    inference(cnf_transformation,[],[f20])).
% 4.97/1.01  fof(f20,axiom,(
% 4.97/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 4.97/1.01  fof(f842,plain,(
% 4.97/1.01    ( ! [X1] : (~r1_tarski(k1_xboole_0,k1_tarski(X1)) | sK3 = X1) ) | ~spl35_20),
% 4.97/1.01    inference(superposition,[],[f229,f795])).
% 4.97/1.01  fof(f795,plain,(
% 4.97/1.01    k1_xboole_0 = k1_tarski(sK3) | ~spl35_20),
% 4.97/1.01    inference(avatar_component_clause,[],[f793])).
% 4.97/1.01  fof(f793,plain,(
% 4.97/1.01    spl35_20 <=> k1_xboole_0 = k1_tarski(sK3)),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_20])])).
% 4.97/1.01  fof(f229,plain,(
% 4.97/1.01    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 4.97/1.01    inference(cnf_transformation,[],[f124])).
% 4.97/1.01  fof(f124,plain,(
% 4.97/1.01    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 4.97/1.01    inference(ennf_transformation,[],[f25])).
% 4.97/1.01  fof(f25,axiom,(
% 4.97/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 4.97/1.01  fof(f877,plain,(
% 4.97/1.01    ( ! [X0,X1] : (k1_xboole_0 != sK3 | r1_tarski(X0,X1)) ) | ~spl35_20),
% 4.97/1.01    inference(backward_demodulation,[],[f251,f858])).
% 4.97/1.01  fof(f251,plain,(
% 4.97/1.01    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 4.97/1.01    inference(cnf_transformation,[],[f7])).
% 4.97/1.01  fof(f7,axiom,(
% 4.97/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.97/1.01  fof(f183,plain,(
% 4.97/1.01    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 4.97/1.01    inference(cnf_transformation,[],[f103])).
% 4.97/1.01  fof(f103,plain,(
% 4.97/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 4.97/1.01    inference(ennf_transformation,[],[f13])).
% 4.97/1.01  fof(f13,axiom,(
% 4.97/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 4.97/1.01  fof(f879,plain,(
% 4.97/1.01    ( ! [X2,X0] : (k1_xboole_0 != sK3 | r2_hidden(X0,X2)) ) | ~spl35_20),
% 4.97/1.01    inference(backward_demodulation,[],[f289,f858])).
% 4.97/1.01  fof(f289,plain,(
% 4.97/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 4.97/1.01    inference(cnf_transformation,[],[f33])).
% 4.97/1.01  fof(f33,axiom,(
% 4.97/1.01    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 4.97/1.01  fof(f1079,plain,(
% 4.97/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) ) | ~spl35_20),
% 4.97/1.01    inference(subsumption_resolution,[],[f929,f1063])).
% 4.97/1.01  fof(f1063,plain,(
% 4.97/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1)) ) | ~spl35_20),
% 4.97/1.01    inference(subsumption_resolution,[],[f220,f1061])).
% 4.97/1.01  fof(f220,plain,(
% 4.97/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 4.97/1.01    inference(cnf_transformation,[],[f115])).
% 4.97/1.01  fof(f115,plain,(
% 4.97/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 4.97/1.01    inference(ennf_transformation,[],[f43])).
% 4.97/1.01  fof(f43,axiom,(
% 4.97/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 4.97/1.01  fof(f929,plain,(
% 4.97/1.01    ( ! [X2,X0,X1] : (~m1_subset_1(X1,sK3) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) ) | ~spl35_20),
% 4.97/1.01    inference(backward_demodulation,[],[f313,f858])).
% 4.97/1.01  fof(f313,plain,(
% 4.97/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.97/1.01    inference(cnf_transformation,[],[f144])).
% 4.97/1.01  fof(f144,plain,(
% 4.97/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.97/1.01    inference(ennf_transformation,[],[f47])).
% 4.97/1.01  fof(f47,axiom,(
% 4.97/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 4.97/1.01  fof(f1005,plain,(
% 4.97/1.01    v1_xboole_0(sK3) | ~spl35_20),
% 4.97/1.01    inference(backward_demodulation,[],[f207,f858])).
% 4.97/1.01  fof(f207,plain,(
% 4.97/1.01    ( ! [X0] : (v1_xboole_0(sK12(X0))) )),
% 4.97/1.01    inference(cnf_transformation,[],[f37])).
% 4.97/1.01  fof(f37,axiom,(
% 4.97/1.01    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 4.97/1.01  fof(f835,plain,(
% 4.97/1.01    spl35_23 | spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_7),
% 4.97/1.01    inference(avatar_split_clause,[],[f818,f388,f375,f370,f365,f360,f832])).
% 4.97/1.01  fof(f360,plain,(
% 4.97/1.01    spl35_1 <=> k1_xboole_0 = sK0),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_1])])).
% 4.97/1.01  fof(f365,plain,(
% 4.97/1.01    spl35_2 <=> k1_xboole_0 = sK1),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_2])])).
% 4.97/1.01  fof(f370,plain,(
% 4.97/1.01    spl35_3 <=> k1_xboole_0 = sK2),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_3])])).
% 4.97/1.01  fof(f375,plain,(
% 4.97/1.01    spl35_4 <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_4])])).
% 4.97/1.01  fof(f388,plain,(
% 4.97/1.01    spl35_7 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_7])])).
% 4.97/1.01  fof(f818,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | (spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_7)),
% 4.97/1.01    inference(subsumption_resolution,[],[f817,f362])).
% 4.97/1.01  fof(f362,plain,(
% 4.97/1.01    k1_xboole_0 != sK0 | spl35_1),
% 4.97/1.01    inference(avatar_component_clause,[],[f360])).
% 4.97/1.01  fof(f817,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_4 | ~spl35_7)),
% 4.97/1.01    inference(subsumption_resolution,[],[f816,f377])).
% 4.97/1.01  fof(f377,plain,(
% 4.97/1.01    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | ~spl35_4),
% 4.97/1.01    inference(avatar_component_clause,[],[f375])).
% 4.97/1.01  fof(f816,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_7)),
% 4.97/1.01    inference(subsumption_resolution,[],[f815,f372])).
% 4.97/1.01  fof(f372,plain,(
% 4.97/1.01    k1_xboole_0 != sK2 | spl35_3),
% 4.97/1.01    inference(avatar_component_clause,[],[f370])).
% 4.97/1.01  fof(f815,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | ~spl35_7)),
% 4.97/1.01    inference(subsumption_resolution,[],[f814,f367])).
% 4.97/1.01  fof(f367,plain,(
% 4.97/1.01    k1_xboole_0 != sK1 | spl35_2),
% 4.97/1.01    inference(avatar_component_clause,[],[f365])).
% 4.97/1.01  fof(f814,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | ~spl35_7),
% 4.97/1.01    inference(superposition,[],[f296,f390])).
% 4.97/1.01  fof(f390,plain,(
% 4.97/1.01    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~spl35_7),
% 4.97/1.01    inference(avatar_component_clause,[],[f388])).
% 4.97/1.01  fof(f296,plain,(
% 4.97/1.01    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 4.97/1.01    inference(cnf_transformation,[],[f138])).
% 4.97/1.01  fof(f138,plain,(
% 4.97/1.01    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 4.97/1.01    inference(ennf_transformation,[],[f85])).
% 4.97/1.01  fof(f85,axiom,(
% 4.97/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 4.97/1.01  fof(f804,plain,(
% 4.97/1.01    spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_14 | spl35_18),
% 4.97/1.01    inference(avatar_contradiction_clause,[],[f803])).
% 4.97/1.01  fof(f803,plain,(
% 4.97/1.01    $false | (spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_14 | spl35_18)),
% 4.97/1.01    inference(subsumption_resolution,[],[f631,f802])).
% 4.97/1.01  fof(f802,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | (spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_14)),
% 4.97/1.01    inference(subsumption_resolution,[],[f801,f362])).
% 4.97/1.01  fof(f801,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_4 | ~spl35_14)),
% 4.97/1.01    inference(subsumption_resolution,[],[f800,f377])).
% 4.97/1.01  fof(f800,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_14)),
% 4.97/1.01    inference(subsumption_resolution,[],[f799,f372])).
% 4.97/1.01  fof(f799,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | ~spl35_14)),
% 4.97/1.01    inference(subsumption_resolution,[],[f689,f367])).
% 4.97/1.01  fof(f689,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | ~spl35_14),
% 4.97/1.01    inference(superposition,[],[f524,f299])).
% 4.97/1.01  fof(f299,plain,(
% 4.97/1.01    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 4.97/1.01    inference(cnf_transformation,[],[f139])).
% 4.97/1.01  fof(f139,plain,(
% 4.97/1.01    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 4.97/1.01    inference(ennf_transformation,[],[f87])).
% 4.97/1.01  fof(f87,axiom,(
% 4.97/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 4.97/1.01  fof(f524,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl35_14),
% 4.97/1.01    inference(avatar_component_clause,[],[f522])).
% 4.97/1.01  fof(f522,plain,(
% 4.97/1.01    spl35_14 <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_14])])).
% 4.97/1.01  fof(f631,plain,(
% 4.97/1.01    sK3 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | spl35_18),
% 4.97/1.01    inference(avatar_component_clause,[],[f630])).
% 4.97/1.01  fof(f630,plain,(
% 4.97/1.01    spl35_18 <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_18])])).
% 4.97/1.01  fof(f796,plain,(
% 4.97/1.01    spl35_20 | ~spl35_18),
% 4.97/1.01    inference(avatar_split_clause,[],[f741,f630,f793])).
% 4.97/1.01  fof(f741,plain,(
% 4.97/1.01    k1_xboole_0 = k1_tarski(sK3) | ~spl35_18),
% 4.97/1.01    inference(subsumption_resolution,[],[f731,f348])).
% 4.97/1.01  fof(f348,plain,(
% 4.97/1.01    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 4.97/1.01    inference(equality_resolution,[],[f286])).
% 4.97/1.01  fof(f286,plain,(
% 4.97/1.01    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 4.97/1.01    inference(cnf_transformation,[],[f137])).
% 4.97/1.01  fof(f137,plain,(
% 4.97/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 4.97/1.01    inference(ennf_transformation,[],[f29])).
% 4.97/1.01  fof(f29,axiom,(
% 4.97/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 4.97/1.01  fof(f731,plain,(
% 4.97/1.01    ( ! [X2] : (~r1_tarski(k1_tarski(sK3),k2_tarski(sK3,k3_mcart_1(X2,sK3,k2_mcart_1(sK3)))) | k1_xboole_0 = k1_tarski(sK3)) ) | ~spl35_18),
% 4.97/1.01    inference(superposition,[],[f276,f674])).
% 4.97/1.01  fof(f674,plain,(
% 4.97/1.01    ( ! [X4] : (k2_tarski(sK3,k3_mcart_1(X4,sK3,k2_mcart_1(sK3))) = k3_zfmisc_1(k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),X4),k1_tarski(sK3),k1_tarski(k2_mcart_1(sK3)))) ) | ~spl35_18),
% 4.97/1.01    inference(superposition,[],[f317,f632])).
% 4.97/1.01  fof(f632,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) | ~spl35_18),
% 4.97/1.01    inference(avatar_component_clause,[],[f630])).
% 4.97/1.01  fof(f317,plain,(
% 4.97/1.01    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))) )),
% 4.97/1.01    inference(cnf_transformation,[],[f82])).
% 4.97/1.01  fof(f82,axiom,(
% 4.97/1.01    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).
% 4.97/1.01  fof(f276,plain,(
% 4.97/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | k1_xboole_0 = X0) )),
% 4.97/1.01    inference(cnf_transformation,[],[f136])).
% 4.97/1.01  fof(f650,plain,(
% 4.97/1.01    spl35_19 | spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_5),
% 4.97/1.01    inference(avatar_split_clause,[],[f644,f380,f375,f370,f365,f360,f647])).
% 4.97/1.01  fof(f380,plain,(
% 4.97/1.01    spl35_5 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_5])])).
% 4.97/1.01  fof(f644,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | (spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_5)),
% 4.97/1.01    inference(subsumption_resolution,[],[f643,f362])).
% 4.97/1.01  fof(f643,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_4 | ~spl35_5)),
% 4.97/1.01    inference(subsumption_resolution,[],[f642,f377])).
% 4.97/1.01  fof(f642,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_5)),
% 4.97/1.01    inference(subsumption_resolution,[],[f641,f372])).
% 4.97/1.01  fof(f641,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | ~spl35_5)),
% 4.97/1.01    inference(subsumption_resolution,[],[f640,f367])).
% 4.97/1.01  fof(f640,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | ~spl35_5),
% 4.97/1.01    inference(superposition,[],[f296,f382])).
% 4.97/1.01  fof(f382,plain,(
% 4.97/1.01    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | ~spl35_5),
% 4.97/1.01    inference(avatar_component_clause,[],[f380])).
% 4.97/1.01  fof(f525,plain,(
% 4.97/1.01    spl35_14 | spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_12),
% 4.97/1.01    inference(avatar_split_clause,[],[f470,f452,f375,f370,f365,f360,f522])).
% 4.97/1.01  fof(f452,plain,(
% 4.97/1.01    spl35_12 <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_12])])).
% 4.97/1.01  fof(f470,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | (spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_12)),
% 4.97/1.01    inference(subsumption_resolution,[],[f469,f362])).
% 4.97/1.01  fof(f469,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_4 | ~spl35_12)),
% 4.97/1.01    inference(subsumption_resolution,[],[f468,f377])).
% 4.97/1.01  fof(f468,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_12)),
% 4.97/1.01    inference(subsumption_resolution,[],[f467,f372])).
% 4.97/1.01  fof(f467,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | ~spl35_12)),
% 4.97/1.01    inference(subsumption_resolution,[],[f456,f367])).
% 4.97/1.01  fof(f456,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | ~spl35_12),
% 4.97/1.01    inference(superposition,[],[f454,f297])).
% 4.97/1.01  fof(f297,plain,(
% 4.97/1.01    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 4.97/1.01    inference(cnf_transformation,[],[f139])).
% 4.97/1.01  fof(f454,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl35_12),
% 4.97/1.01    inference(avatar_component_clause,[],[f452])).
% 4.97/1.01  fof(f455,plain,(
% 4.97/1.01    spl35_12 | spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_6),
% 4.97/1.01    inference(avatar_split_clause,[],[f450,f384,f375,f370,f365,f360,f452])).
% 4.97/1.01  fof(f384,plain,(
% 4.97/1.01    spl35_6 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 4.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl35_6])])).
% 4.97/1.01  fof(f450,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | (spl35_1 | spl35_2 | spl35_3 | ~spl35_4 | ~spl35_6)),
% 4.97/1.01    inference(subsumption_resolution,[],[f449,f362])).
% 4.97/1.01  fof(f449,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_4 | ~spl35_6)),
% 4.97/1.01    inference(subsumption_resolution,[],[f448,f377])).
% 4.97/1.01  fof(f448,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | spl35_3 | ~spl35_6)),
% 4.97/1.01    inference(subsumption_resolution,[],[f447,f372])).
% 4.97/1.01  fof(f447,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl35_2 | ~spl35_6)),
% 4.97/1.01    inference(subsumption_resolution,[],[f446,f367])).
% 4.97/1.01  fof(f446,plain,(
% 4.97/1.01    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | ~spl35_6),
% 4.97/1.01    inference(superposition,[],[f296,f386])).
% 4.97/1.01  fof(f386,plain,(
% 4.97/1.01    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | ~spl35_6),
% 4.97/1.01    inference(avatar_component_clause,[],[f384])).
% 4.97/1.01  fof(f391,plain,(
% 4.97/1.01    spl35_5 | spl35_6 | spl35_7),
% 4.97/1.01    inference(avatar_split_clause,[],[f151,f388,f384,f380])).
% 4.97/1.01  fof(f151,plain,(
% 4.97/1.01    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 4.97/1.01    inference(cnf_transformation,[],[f91])).
% 4.97/1.01  fof(f91,plain,(
% 4.97/1.01    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 4.97/1.01    inference(ennf_transformation,[],[f89])).
% 4.97/1.01  fof(f89,negated_conjecture,(
% 4.97/1.01    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 4.97/1.01    inference(negated_conjecture,[],[f88])).
% 4.97/1.01  fof(f88,conjecture,(
% 4.97/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 4.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 4.97/1.01  fof(f378,plain,(
% 4.97/1.01    spl35_4),
% 4.97/1.01    inference(avatar_split_clause,[],[f152,f375])).
% 4.97/1.01  fof(f152,plain,(
% 4.97/1.01    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 4.97/1.01    inference(cnf_transformation,[],[f91])).
% 4.97/1.01  fof(f373,plain,(
% 4.97/1.01    ~spl35_3),
% 4.97/1.01    inference(avatar_split_clause,[],[f155,f370])).
% 4.97/1.01  fof(f155,plain,(
% 4.97/1.01    k1_xboole_0 != sK2),
% 4.97/1.01    inference(cnf_transformation,[],[f91])).
% 4.97/1.01  fof(f368,plain,(
% 4.97/1.01    ~spl35_2),
% 4.97/1.01    inference(avatar_split_clause,[],[f154,f365])).
% 4.97/1.01  fof(f154,plain,(
% 4.97/1.01    k1_xboole_0 != sK1),
% 4.97/1.01    inference(cnf_transformation,[],[f91])).
% 4.97/1.01  fof(f363,plain,(
% 4.97/1.01    ~spl35_1),
% 4.97/1.01    inference(avatar_split_clause,[],[f153,f360])).
% 4.97/1.01  fof(f153,plain,(
% 4.97/1.01    k1_xboole_0 != sK0),
% 4.97/1.01    inference(cnf_transformation,[],[f91])).
% 4.97/1.01  % SZS output end Proof for theBenchmark
% 4.97/1.01  % (1528)------------------------------
% 4.97/1.01  % (1528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.01  % (1528)Termination reason: Refutation
% 4.97/1.01  
% 4.97/1.01  % (1528)Memory used [KB]: 14456
% 4.97/1.01  % (1528)Time elapsed: 0.567 s
% 4.97/1.01  % (1528)------------------------------
% 4.97/1.01  % (1528)------------------------------
% 4.97/1.02  % (1507)Success in time 0.644 s
%------------------------------------------------------------------------------
