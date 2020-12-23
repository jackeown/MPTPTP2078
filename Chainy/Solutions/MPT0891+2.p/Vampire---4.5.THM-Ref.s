%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0891+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 10.23s
% Output     : Refutation 10.23s
% Verified   : 
% Statistics : Number of formulae       :  730 (2130 expanded)
%              Number of leaves         :  186 ( 890 expanded)
%              Depth                    :   13
%              Number of atoms          : 2104 (6051 expanded)
%              Number of equality atoms :  393 (1995 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1897,f1902,f1907,f1912,f1917,f1922,f1927,f1932,f1937,f1942,f1947,f1952,f1970,f1975,f2027,f2050,f2128,f2189,f2221,f2365,f2395,f2427,f2504,f2537,f2587,f2597,f2715,f2844,f2852,f2857,f2880,f2924,f3015,f3052,f3081,f3103,f3214,f3367,f3493,f3592,f3632,f3732,f3890,f4151,f4226,f4380,f4452,f4751,f4943,f5022,f5150,f5339,f5344,f5353,f5361,f5366,f5371,f5408,f5417,f5422,f5483,f5488,f5493,f5503,f5508,f5513,f5533,f5541,f5551,f5561,f5565,f5573,f5691,f5749,f5750,f5774,f5789,f5824,f5837,f5863,f5874,f5934,f5942,f5948,f5966,f6004,f6184,f6317,f6322,f6376,f6381,f6511,f6621,f6645,f6735,f6876,f6883,f6890,f7014,f7154,f7203,f7324,f7459,f7511,f7513,f7519,f7521,f7528,f7550,f7555,f7558,f7567,f7576,f7581,f7589,f7605,f7608,f7655,f7660,f7665,f7682,f7687,f7727,f7736,f7782,f7838,f7840,f7886,f7892,f7908,f7915,f7926,f7935,f7940,f8030])).

fof(f8030,plain,(
    ~ spl55_136 ),
    inference(avatar_contradiction_clause,[],[f8029])).

fof(f8029,plain,
    ( $false
    | ~ spl55_136 ),
    inference(subsumption_resolution,[],[f8027,f1857])).

fof(f1857,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1652])).

fof(f1652,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f8027,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | ~ spl55_136 ),
    inference(superposition,[],[f3209,f7939])).

fof(f7939,plain,
    ( sK3 = k3_mcart_1(sK3,k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | ~ spl55_136 ),
    inference(avatar_component_clause,[],[f7937])).

fof(f7937,plain,
    ( spl55_136
  <=> sK3 = k3_mcart_1(sK3,k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_136])])).

fof(f3209,plain,(
    ! [X12,X10,X11] : ~ r1_tarski(k1_tarski(X10),k1_tarski(k3_mcart_1(X10,X11,X12))) ),
    inference(subsumption_resolution,[],[f3204,f1979])).

fof(f1979,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f1678,f1679])).

fof(f1679,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f1353])).

fof(f1353,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f1678,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f3204,plain,(
    ! [X12,X10,X11] :
      ( ~ r1_tarski(k1_tarski(X10),k1_tarski(k3_mcart_1(X10,X11,X12)))
      | k1_xboole_0 = k1_tarski(X10) ) ),
    inference(superposition,[],[f1619,f1622])).

fof(f1622,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f1332])).

fof(f1332,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

fof(f1619,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1422])).

fof(f1422,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f1343])).

fof(f1343,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f7940,plain,
    ( spl55_136
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_67
    | ~ spl55_121 ),
    inference(avatar_split_clause,[],[f7836,f7578,f5485,f5358,f1909,f1904,f1899,f1894,f7937])).

fof(f1894,plain,
    ( spl55_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_1])])).

fof(f1899,plain,
    ( spl55_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_2])])).

fof(f1904,plain,
    ( spl55_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_3])])).

fof(f1909,plain,
    ( spl55_4
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_4])])).

fof(f5358,plain,
    ( spl55_59
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_59])])).

fof(f5485,plain,
    ( spl55_67
  <=> sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_67])])).

fof(f7578,plain,
    ( spl55_121
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_121])])).

fof(f7836,plain,
    ( sK3 = k3_mcart_1(sK3,k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_67
    | ~ spl55_121 ),
    inference(backward_demodulation,[],[f7787,f5486])).

fof(f5486,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl55_67 ),
    inference(avatar_component_clause,[],[f5485])).

fof(f7787,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_121 ),
    inference(forward_demodulation,[],[f7460,f7580])).

fof(f7580,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl55_121 ),
    inference(avatar_component_clause,[],[f7578])).

fof(f7460,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59 ),
    inference(forward_demodulation,[],[f5193,f5360])).

fof(f5360,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl55_59 ),
    inference(avatar_component_clause,[],[f5358])).

fof(f5193,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(forward_demodulation,[],[f5192,f4734])).

fof(f4734,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4733,f1896])).

fof(f1896,plain,
    ( k1_xboole_0 != sK0
    | spl55_1 ),
    inference(avatar_component_clause,[],[f1894])).

fof(f4733,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4732,f1906])).

fof(f1906,plain,
    ( k1_xboole_0 != sK2
    | spl55_3 ),
    inference(avatar_component_clause,[],[f1904])).

fof(f4732,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | spl55_2
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4719,f1901])).

fof(f1901,plain,
    ( k1_xboole_0 != sK1
    | spl55_2 ),
    inference(avatar_component_clause,[],[f1899])).

fof(f4719,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | ~ spl55_4 ),
    inference(resolution,[],[f1529,f1911])).

fof(f1911,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_4 ),
    inference(avatar_component_clause,[],[f1909])).

fof(f1529,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f1358])).

fof(f1358,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1345])).

fof(f1345,axiom,(
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

fof(f5192,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f5191,f1896])).

fof(f5191,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f5190,f1906])).

fof(f5190,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_2
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f5177,f1901])).

fof(f5177,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl55_4 ),
    inference(resolution,[],[f1530,f1911])).

fof(f1530,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f1359])).

fof(f1359,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1342])).

fof(f1342,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f7935,plain,
    ( spl55_135
    | ~ spl55_67
    | ~ spl55_88 ),
    inference(avatar_split_clause,[],[f7823,f5871,f5485,f7932])).

fof(f7932,plain,
    ( spl55_135
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_135])])).

fof(f5871,plain,
    ( spl55_88
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_88])])).

fof(f7823,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl55_67
    | ~ spl55_88 ),
    inference(backward_demodulation,[],[f5873,f5486])).

fof(f5873,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),sK0)
    | ~ spl55_88 ),
    inference(avatar_component_clause,[],[f5871])).

fof(f7926,plain,
    ( ~ spl55_134
    | ~ spl55_67
    | spl55_122 ),
    inference(avatar_split_clause,[],[f7835,f7586,f5485,f7923])).

fof(f7923,plain,
    ( spl55_134
  <=> sK3 = k3_mcart_1(sK3,k2_mcart_1(k1_mcart_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_134])])).

fof(f7586,plain,
    ( spl55_122
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_122])])).

fof(f7835,plain,
    ( sK3 != k3_mcart_1(sK3,k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | ~ spl55_67
    | spl55_122 ),
    inference(backward_demodulation,[],[f7587,f5486])).

fof(f7587,plain,
    ( sK3 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | spl55_122 ),
    inference(avatar_component_clause,[],[f7586])).

fof(f7915,plain,
    ( ~ spl55_133
    | spl55_61
    | ~ spl55_67 ),
    inference(avatar_split_clause,[],[f7791,f5485,f5368,f7912])).

fof(f7912,plain,
    ( spl55_133
  <=> sK3 = k3_mcart_1(sK3,sK3,k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_133])])).

fof(f5368,plain,
    ( spl55_61
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_61])])).

fof(f7791,plain,
    ( sK3 != k3_mcart_1(sK3,sK3,k2_mcart_1(sK3))
    | spl55_61
    | ~ spl55_67 ),
    inference(backward_demodulation,[],[f5369,f5486])).

fof(f5369,plain,
    ( sK3 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | spl55_61 ),
    inference(avatar_component_clause,[],[f5368])).

fof(f7908,plain,
    ( spl55_15
    | ~ spl55_59
    | ~ spl55_67 ),
    inference(avatar_split_clause,[],[f7790,f5485,f5358,f1967])).

fof(f1967,plain,
    ( spl55_15
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_15])])).

fof(f7790,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl55_59
    | ~ spl55_67 ),
    inference(backward_demodulation,[],[f5360,f5486])).

fof(f7892,plain,
    ( ~ spl55_132
    | ~ spl55_67
    | spl55_119 ),
    inference(avatar_split_clause,[],[f7831,f7564,f5485,f7889])).

fof(f7889,plain,
    ( spl55_132
  <=> sK3 = k3_mcart_1(sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_132])])).

fof(f7564,plain,
    ( spl55_119
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_119])])).

fof(f7831,plain,
    ( sK3 != k3_mcart_1(sK3,sK3,sK3)
    | ~ spl55_67
    | spl55_119 ),
    inference(backward_demodulation,[],[f7566,f5486])).

fof(f7566,plain,
    ( sK3 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,sK3)
    | spl55_119 ),
    inference(avatar_component_clause,[],[f7564])).

fof(f7886,plain,
    ( spl55_131
    | ~ spl55_67
    | ~ spl55_70 ),
    inference(avatar_split_clause,[],[f7794,f5505,f5485,f7883])).

fof(f7883,plain,
    ( spl55_131
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_131])])).

fof(f5505,plain,
    ( spl55_70
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_70])])).

fof(f7794,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl55_67
    | ~ spl55_70 ),
    inference(backward_demodulation,[],[f5507,f5486])).

fof(f5507,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK3)),sK0)
    | ~ spl55_70 ),
    inference(avatar_component_clause,[],[f5505])).

fof(f7840,plain,
    ( spl55_64
    | ~ spl55_67 ),
    inference(avatar_contradiction_clause,[],[f7839])).

fof(f7839,plain,
    ( $false
    | spl55_64
    | ~ spl55_67 ),
    inference(subsumption_resolution,[],[f7793,f1866])).

fof(f1866,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1665])).

fof(f1665,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7793,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl55_64
    | ~ spl55_67 ),
    inference(backward_demodulation,[],[f5416,f5486])).

fof(f5416,plain,
    ( ~ r1_tarski(sK3,k1_mcart_1(k1_mcart_1(sK3)))
    | spl55_64 ),
    inference(avatar_component_clause,[],[f5414])).

fof(f5414,plain,
    ( spl55_64
  <=> r1_tarski(sK3,k1_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_64])])).

fof(f7838,plain,
    ( spl55_63
    | ~ spl55_67 ),
    inference(avatar_contradiction_clause,[],[f7837])).

fof(f7837,plain,
    ( $false
    | spl55_63
    | ~ spl55_67 ),
    inference(subsumption_resolution,[],[f7792,f1866])).

fof(f7792,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl55_63
    | ~ spl55_67 ),
    inference(backward_demodulation,[],[f5412,f5486])).

fof(f5412,plain,
    ( ~ r1_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)
    | spl55_63 ),
    inference(avatar_component_clause,[],[f5410])).

fof(f5410,plain,
    ( spl55_63
  <=> r1_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_63])])).

fof(f7782,plain,
    ( spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_60
    | ~ spl55_121
    | spl55_122 ),
    inference(avatar_contradiction_clause,[],[f7781])).

fof(f7781,plain,
    ( $false
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_60
    | ~ spl55_121
    | spl55_122 ),
    inference(subsumption_resolution,[],[f7587,f7740])).

fof(f7740,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_60
    | ~ spl55_121 ),
    inference(forward_demodulation,[],[f7739,f7580])).

fof(f7739,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | ~ spl55_60 ),
    inference(forward_demodulation,[],[f7460,f5364])).

fof(f5364,plain,
    ( sK3 = k2_mcart_1(sK3)
    | ~ spl55_60 ),
    inference(avatar_component_clause,[],[f5363])).

fof(f5363,plain,
    ( spl55_60
  <=> sK3 = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_60])])).

fof(f7736,plain,(
    ~ spl55_122 ),
    inference(avatar_contradiction_clause,[],[f7735])).

fof(f7735,plain,
    ( $false
    | ~ spl55_122 ),
    inference(subsumption_resolution,[],[f7733,f1857])).

fof(f7733,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | ~ spl55_122 ),
    inference(superposition,[],[f3208,f7588])).

fof(f7588,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | ~ spl55_122 ),
    inference(avatar_component_clause,[],[f7586])).

fof(f3208,plain,(
    ! [X8,X7,X9] : ~ r1_tarski(k1_tarski(X9),k1_tarski(k3_mcart_1(X7,X8,X9))) ),
    inference(subsumption_resolution,[],[f3203,f1979])).

fof(f3203,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(k1_tarski(X9),k1_tarski(k3_mcart_1(X7,X8,X9)))
      | k1_xboole_0 = k1_tarski(X9) ) ),
    inference(superposition,[],[f1620,f1622])).

fof(f1620,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1422])).

fof(f7727,plain,
    ( ~ spl55_130
    | spl55_19
    | ~ spl55_41 ),
    inference(avatar_split_clause,[],[f6337,f3490,f2043,f7724])).

fof(f7724,plain,
    ( spl55_130
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_130])])).

fof(f2043,plain,
    ( spl55_19
  <=> v3_ordinal1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_19])])).

fof(f3490,plain,
    ( spl55_41
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_41])])).

fof(f6337,plain,
    ( v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK1)
    | ~ spl55_41 ),
    inference(resolution,[],[f2006,f3492])).

fof(f3492,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl55_41 ),
    inference(avatar_component_clause,[],[f3490])).

fof(f2006,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | v3_ordinal1(X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f1593,f1575])).

fof(f1575,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f1593,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f1415])).

fof(f1415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1058])).

fof(f1058,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_ordinal1)).

fof(f7687,plain,
    ( spl55_53
    | spl55_128
    | spl55_129 ),
    inference(avatar_contradiction_clause,[],[f7686])).

fof(f7686,plain,
    ( $false
    | spl55_53
    | spl55_128
    | spl55_129 ),
    inference(subsumption_resolution,[],[f7685,f5020])).

fof(f5020,plain,
    ( sK3 != k2_mcart_1(k1_mcart_1(sK3))
    | spl55_53 ),
    inference(avatar_component_clause,[],[f5019])).

fof(f5019,plain,
    ( spl55_53
  <=> sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_53])])).

fof(f7685,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_128
    | spl55_129 ),
    inference(subsumption_resolution,[],[f7684,f7677])).

fof(f7677,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | spl55_128 ),
    inference(avatar_component_clause,[],[f7675])).

fof(f7675,plain,
    ( spl55_128
  <=> r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_128])])).

fof(f7684,plain,
    ( r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_129 ),
    inference(resolution,[],[f7681,f1667])).

fof(f1667,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK35(X0,X1),X1)
      | r2_hidden(sK35(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f7681,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),k2_mcart_1(k1_mcart_1(sK3)))
    | spl55_129 ),
    inference(avatar_component_clause,[],[f7679])).

fof(f7679,plain,
    ( spl55_129
  <=> r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),k2_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_129])])).

fof(f7682,plain,
    ( ~ spl55_128
    | ~ spl55_129
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(avatar_split_clause,[],[f7536,f1963,f1909,f1904,f1899,f1894,f7679,f7675])).

fof(f1963,plain,
    ( spl55_14
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_14])])).

fof(f7536,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),k2_mcart_1(k1_mcart_1(sK3)))
    | ~ r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(forward_demodulation,[],[f7535,f4964])).

fof(f4964,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4963,f1896])).

fof(f4963,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4962,f1906])).

fof(f4962,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_2
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4949,f1901])).

fof(f4949,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl55_4 ),
    inference(resolution,[],[f1528,f1911])).

fof(f1528,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f1358])).

fof(f7535,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | ~ r2_hidden(sK35(k6_mcart_1(sK0,sK1,sK2,sK3),sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(forward_demodulation,[],[f7530,f4964])).

fof(f7530,plain,
    ( ~ r2_hidden(sK35(k6_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3)
    | ~ r2_hidden(sK35(k6_mcart_1(sK0,sK1,sK2,sK3),sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_14 ),
    inference(extensionality_resolution,[],[f1668,f1964])).

fof(f1964,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | spl55_14 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f1668,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK35(X0,X1),X1)
      | ~ r2_hidden(sK35(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f7665,plain,
    ( spl55_127
    | spl55_68
    | spl55_69
    | ~ spl55_101 ),
    inference(avatar_split_clause,[],[f7506,f6378,f5500,f5496,f7662])).

fof(f7662,plain,
    ( spl55_127
  <=> v3_ordinal1(sK35(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_127])])).

fof(f5496,plain,
    ( spl55_68
  <=> r2_hidden(sK35(k2_mcart_1(sK3),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_68])])).

fof(f5500,plain,
    ( spl55_69
  <=> r2_hidden(sK35(k2_mcart_1(sK3),sK3),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_69])])).

fof(f6378,plain,
    ( spl55_101
  <=> v3_ordinal1(sK35(sK3,k2_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_101])])).

fof(f7506,plain,
    ( v3_ordinal1(sK35(sK3,sK3))
    | spl55_68
    | spl55_69
    | ~ spl55_101 ),
    inference(backward_demodulation,[],[f6380,f5511])).

fof(f5511,plain,
    ( sK3 = k2_mcart_1(sK3)
    | spl55_68
    | spl55_69 ),
    inference(subsumption_resolution,[],[f5510,f5498])).

fof(f5498,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(sK3),sK3),sK3)
    | spl55_68 ),
    inference(avatar_component_clause,[],[f5496])).

fof(f5510,plain,
    ( r2_hidden(sK35(k2_mcart_1(sK3),sK3),sK3)
    | sK3 = k2_mcart_1(sK3)
    | spl55_69 ),
    inference(resolution,[],[f5502,f1667])).

fof(f5502,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(sK3),sK3),k2_mcart_1(sK3))
    | spl55_69 ),
    inference(avatar_component_clause,[],[f5500])).

fof(f6380,plain,
    ( v3_ordinal1(sK35(sK3,k2_mcart_1(sK3)))
    | ~ spl55_101 ),
    inference(avatar_component_clause,[],[f6378])).

fof(f7660,plain,
    ( spl55_53
    | spl55_125
    | spl55_126 ),
    inference(avatar_contradiction_clause,[],[f7659])).

fof(f7659,plain,
    ( $false
    | spl55_53
    | spl55_125
    | spl55_126 ),
    inference(subsumption_resolution,[],[f7658,f5020])).

fof(f7658,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_125
    | spl55_126 ),
    inference(subsumption_resolution,[],[f7657,f7654])).

fof(f7654,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),sK3)
    | spl55_126 ),
    inference(avatar_component_clause,[],[f7652])).

fof(f7652,plain,
    ( spl55_126
  <=> r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_126])])).

fof(f7657,plain,
    ( r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_125 ),
    inference(resolution,[],[f7650,f1667])).

fof(f7650,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(k1_mcart_1(sK3)))
    | spl55_125 ),
    inference(avatar_component_clause,[],[f7648])).

fof(f7648,plain,
    ( spl55_125
  <=> r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_125])])).

fof(f7655,plain,
    ( ~ spl55_125
    | ~ spl55_126
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(avatar_split_clause,[],[f7534,f1963,f1909,f1904,f1899,f1894,f7652,f7648])).

fof(f7534,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),sK3)
    | ~ r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(k1_mcart_1(sK3)))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(forward_demodulation,[],[f7533,f4964])).

fof(f7533,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(k1_mcart_1(sK3)))
    | ~ r2_hidden(sK35(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(forward_demodulation,[],[f7529,f4964])).

fof(f7529,plain,
    ( ~ r2_hidden(sK35(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ r2_hidden(sK35(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | spl55_14 ),
    inference(extensionality_resolution,[],[f1668,f1964])).

fof(f7608,plain,
    ( spl55_60
    | spl55_68
    | spl55_69 ),
    inference(avatar_split_clause,[],[f5511,f5500,f5496,f5363])).

fof(f7605,plain,
    ( ~ spl55_123
    | ~ spl55_124
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(avatar_split_clause,[],[f7538,f1963,f1909,f1904,f1899,f1894,f7602,f7598])).

fof(f7598,plain,
    ( spl55_123
  <=> r1_tarski(k2_mcart_1(k1_mcart_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_123])])).

fof(f7602,plain,
    ( spl55_124
  <=> r1_tarski(sK3,k2_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_124])])).

fof(f7538,plain,
    ( ~ r1_tarski(sK3,k2_mcart_1(k1_mcart_1(sK3)))
    | ~ r1_tarski(k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(forward_demodulation,[],[f7537,f4964])).

fof(f7537,plain,
    ( ~ r1_tarski(k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | ~ r1_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14 ),
    inference(forward_demodulation,[],[f7531,f4964])).

fof(f7531,plain,
    ( ~ r1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_14 ),
    inference(extensionality_resolution,[],[f1666,f1964])).

fof(f1666,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7589,plain,
    ( spl55_122
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | spl55_68
    | spl55_69 ),
    inference(avatar_split_clause,[],[f7524,f5500,f5496,f5358,f1909,f1904,f1899,f1894,f7586])).

fof(f7524,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f7522,f4964])).

fof(f7522,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_59
    | spl55_68
    | spl55_69 ),
    inference(forward_demodulation,[],[f7460,f5511])).

fof(f7581,plain,
    ( spl55_121
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f4964,f1909,f1904,f1899,f1894,f7578])).

fof(f7576,plain,
    ( spl55_120
    | spl55_68
    | spl55_69
    | ~ spl55_82 ),
    inference(avatar_split_clause,[],[f7492,f5771,f5500,f5496,f7573])).

fof(f7573,plain,
    ( spl55_120
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_120])])).

fof(f5771,plain,
    ( spl55_82
  <=> r2_hidden(k2_mcart_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_82])])).

fof(f7492,plain,
    ( r2_hidden(sK3,sK2)
    | spl55_68
    | spl55_69
    | ~ spl55_82 ),
    inference(backward_demodulation,[],[f5773,f5511])).

fof(f5773,plain,
    ( r2_hidden(k2_mcart_1(sK3),sK2)
    | ~ spl55_82 ),
    inference(avatar_component_clause,[],[f5771])).

fof(f7567,plain,
    ( ~ spl55_119
    | spl55_61
    | spl55_68
    | spl55_69 ),
    inference(avatar_split_clause,[],[f7517,f5500,f5496,f5368,f7564])).

fof(f7517,plain,
    ( sK3 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,sK3)
    | spl55_61
    | spl55_68
    | spl55_69 ),
    inference(forward_demodulation,[],[f5369,f5511])).

fof(f7558,plain,
    ( spl55_13
    | ~ spl55_56
    | spl55_68
    | spl55_69 ),
    inference(avatar_split_clause,[],[f7467,f5500,f5496,f5341,f1959])).

fof(f1959,plain,
    ( spl55_13
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_13])])).

fof(f5341,plain,
    ( spl55_56
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_56])])).

fof(f7467,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl55_56
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f5343,f5511])).

fof(f5343,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | ~ spl55_56 ),
    inference(avatar_component_clause,[],[f5341])).

fof(f7555,plain,
    ( ~ spl55_118
    | spl55_65
    | spl55_68
    | spl55_69 ),
    inference(avatar_split_clause,[],[f7474,f5500,f5496,f5476,f7552])).

fof(f7552,plain,
    ( spl55_118
  <=> r2_hidden(sK35(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_118])])).

fof(f5476,plain,
    ( spl55_65
  <=> r2_hidden(sK35(sK3,k2_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_65])])).

fof(f7474,plain,
    ( ~ r2_hidden(sK35(sK3,sK3),sK3)
    | spl55_65
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f5478,f5511])).

fof(f5478,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl55_65 ),
    inference(avatar_component_clause,[],[f5476])).

fof(f7550,plain,
    ( spl55_117
    | ~ spl55_62
    | spl55_68
    | spl55_69 ),
    inference(avatar_split_clause,[],[f7470,f5500,f5496,f5405,f7547])).

fof(f7547,plain,
    ( spl55_117
  <=> m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_117])])).

fof(f5405,plain,
    ( spl55_62
  <=> m1_subset_1(k2_mcart_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_62])])).

fof(f7470,plain,
    ( m1_subset_1(sK3,sK2)
    | ~ spl55_62
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f5407,f5511])).

fof(f5407,plain,
    ( m1_subset_1(k2_mcart_1(sK3),sK2)
    | ~ spl55_62 ),
    inference(avatar_component_clause,[],[f5405])).

fof(f7528,plain,
    ( ~ spl55_19
    | spl55_68
    | spl55_69
    | spl55_75 ),
    inference(avatar_split_clause,[],[f7477,f5554,f5500,f5496,f2043])).

fof(f5554,plain,
    ( spl55_75
  <=> v3_ordinal1(k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_75])])).

fof(f7477,plain,
    ( ~ v3_ordinal1(sK3)
    | spl55_68
    | spl55_69
    | spl55_75 ),
    inference(backward_demodulation,[],[f5555,f5511])).

fof(f5555,plain,
    ( ~ v3_ordinal1(k2_mcart_1(sK3))
    | spl55_75 ),
    inference(avatar_component_clause,[],[f5554])).

fof(f7521,plain,
    ( spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14
    | ~ spl55_53 ),
    inference(avatar_contradiction_clause,[],[f7520])).

fof(f7520,plain,
    ( $false
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_14
    | ~ spl55_53 ),
    inference(subsumption_resolution,[],[f1964,f7461])).

fof(f7461,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_53 ),
    inference(forward_demodulation,[],[f4964,f5021])).

fof(f5021,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl55_53 ),
    inference(avatar_component_clause,[],[f5019])).

fof(f7519,plain,
    ( spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_53
    | ~ spl55_59
    | spl55_61
    | spl55_68
    | spl55_69 ),
    inference(avatar_contradiction_clause,[],[f7518])).

fof(f7518,plain,
    ( $false
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_53
    | ~ spl55_59
    | spl55_61
    | spl55_68
    | spl55_69 ),
    inference(subsumption_resolution,[],[f7517,f7509])).

fof(f7509,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_53
    | ~ spl55_59
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f7463,f5511])).

fof(f7463,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_53
    | ~ spl55_59 ),
    inference(backward_demodulation,[],[f7460,f7461])).

fof(f7513,plain,
    ( spl55_58
    | spl55_68
    | spl55_69 ),
    inference(avatar_contradiction_clause,[],[f7512])).

fof(f7512,plain,
    ( $false
    | spl55_58
    | spl55_68
    | spl55_69 ),
    inference(subsumption_resolution,[],[f7469,f1866])).

fof(f7469,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl55_58
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f5352,f5511])).

fof(f5352,plain,
    ( ~ r1_tarski(sK3,k2_mcart_1(sK3))
    | spl55_58 ),
    inference(avatar_component_clause,[],[f5350])).

fof(f5350,plain,
    ( spl55_58
  <=> r1_tarski(sK3,k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_58])])).

fof(f7511,plain,
    ( spl55_57
    | spl55_68
    | spl55_69 ),
    inference(avatar_contradiction_clause,[],[f7510])).

fof(f7510,plain,
    ( $false
    | spl55_57
    | spl55_68
    | spl55_69 ),
    inference(subsumption_resolution,[],[f7468,f1866])).

fof(f7468,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl55_57
    | spl55_68
    | spl55_69 ),
    inference(backward_demodulation,[],[f5348,f5511])).

fof(f5348,plain,
    ( ~ r1_tarski(k2_mcart_1(sK3),sK3)
    | spl55_57 ),
    inference(avatar_component_clause,[],[f5346])).

fof(f5346,plain,
    ( spl55_57
  <=> r1_tarski(k2_mcart_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_57])])).

fof(f7459,plain,(
    ~ spl55_61 ),
    inference(avatar_contradiction_clause,[],[f7458])).

fof(f7458,plain,
    ( $false
    | ~ spl55_61 ),
    inference(subsumption_resolution,[],[f7455,f1857])).

fof(f7455,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | ~ spl55_61 ),
    inference(superposition,[],[f3207,f5370])).

fof(f5370,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | ~ spl55_61 ),
    inference(avatar_component_clause,[],[f5368])).

fof(f3207,plain,(
    ! [X6,X4,X5] : ~ r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X4,X5,X6))) ),
    inference(subsumption_resolution,[],[f3202,f1979])).

fof(f3202,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X4,X5,X6)))
      | k1_xboole_0 = k1_tarski(X5) ) ),
    inference(superposition,[],[f1621,f1622])).

fof(f1621,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1422])).

fof(f7324,plain,
    ( ~ spl55_115
    | spl55_116
    | ~ spl55_66 ),
    inference(avatar_split_clause,[],[f7053,f5480,f7321,f7317])).

fof(f7317,plain,
    ( spl55_115
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_115])])).

fof(f7321,plain,
    ( spl55_116
  <=> v1_relat_1(k1_tarski(sK35(sK3,k2_mcart_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_116])])).

fof(f5480,plain,
    ( spl55_66
  <=> r2_hidden(sK35(sK3,k2_mcart_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_66])])).

fof(f7053,plain,
    ( v1_relat_1(k1_tarski(sK35(sK3,k2_mcart_1(sK3))))
    | ~ v1_relat_1(sK3)
    | ~ spl55_66 ),
    inference(resolution,[],[f2181,f5481])).

fof(f5481,plain,
    ( r2_hidden(sK35(sK3,k2_mcart_1(sK3)),sK3)
    | ~ spl55_66 ),
    inference(avatar_component_clause,[],[f5480])).

fof(f2181,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X11,X10)
      | v1_relat_1(k1_tarski(X11))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f1591,f1574])).

fof(f1574,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1398])).

fof(f1398,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f1591,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1413])).

fof(f1413,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f7203,plain,
    ( spl55_94
    | spl55_114 ),
    inference(avatar_split_clause,[],[f2300,f7201,f5964])).

fof(f5964,plain,
    ( spl55_94
  <=> ! [X9] : ~ v1_xboole_0(k1_zfmisc_1(X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_94])])).

fof(f7201,plain,
    ( spl55_114
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X3,X4)
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_114])])).

fof(f2300,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v1_xboole_0(X4)
      | ~ v1_xboole_0(k1_zfmisc_1(X5)) ) ),
    inference(subsumption_resolution,[],[f2291,f2018])).

fof(f2018,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(k1_zfmisc_1(X2))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f2016,f1595])).

fof(f1595,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK25(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1416])).

fof(f1416,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f489])).

fof(f489,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f2016,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | v1_xboole_0(sK25(X2))
      | ~ v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f1594,f1583])).

fof(f1583,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1410,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1594,plain,(
    ! [X0] :
      ( m1_subset_1(sK25(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1416])).

fof(f2291,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v1_xboole_0(X5)
      | ~ v1_xboole_0(X4)
      | ~ v1_xboole_0(k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f1551,f1582])).

fof(f1582,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1551,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f1378])).

fof(f1378,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f7154,plain,
    ( ~ spl55_112
    | spl55_113
    | ~ spl55_88 ),
    inference(avatar_split_clause,[],[f7030,f5871,f7151,f7147])).

fof(f7147,plain,
    ( spl55_112
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_112])])).

fof(f7151,plain,
    ( spl55_113
  <=> v1_relat_1(k1_tarski(k1_mcart_1(k1_mcart_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_113])])).

fof(f7030,plain,
    ( v1_relat_1(k1_tarski(k1_mcart_1(k1_mcart_1(sK3))))
    | ~ v1_relat_1(sK0)
    | ~ spl55_88 ),
    inference(resolution,[],[f2181,f5873])).

fof(f7014,plain,
    ( spl55_111
    | spl55_2
    | ~ spl55_41 ),
    inference(avatar_split_clause,[],[f4664,f3490,f1899,f7011])).

fof(f7011,plain,
    ( spl55_111
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK45(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_111])])).

fof(f4664,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK45(sK1),sK3),sK1)
    | spl55_2
    | ~ spl55_41 ),
    inference(subsumption_resolution,[],[f4649,f1901])).

fof(f4649,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK45(sK1),sK3),sK1)
    | k1_xboole_0 = sK1
    | ~ spl55_41 ),
    inference(resolution,[],[f3550,f1785])).

fof(f1785,plain,(
    ! [X0] :
      ( r2_hidden(sK45(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1483])).

fof(f1483,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f1482])).

fof(f1482,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1349])).

fof(f1349,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f3550,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,sK3),sK1) )
    | ~ spl55_41 ),
    inference(resolution,[],[f3492,f1702])).

fof(f1702,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f429])).

fof(f429,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f6890,plain,
    ( ~ spl55_5
    | ~ spl55_21
    | ~ spl55_110 ),
    inference(avatar_contradiction_clause,[],[f6889])).

fof(f6889,plain,
    ( $false
    | ~ spl55_5
    | ~ spl55_21
    | ~ spl55_110 ),
    inference(subsumption_resolution,[],[f6884,f1916])).

fof(f1916,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl55_5 ),
    inference(avatar_component_clause,[],[f1914])).

fof(f1914,plain,
    ( spl55_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_5])])).

fof(f6884,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl55_21
    | ~ spl55_110 ),
    inference(resolution,[],[f6882,f2124])).

fof(f2124,plain,
    ( v3_ordinal1(k1_xboole_0)
    | ~ spl55_21 ),
    inference(avatar_component_clause,[],[f2122])).

fof(f2122,plain,
    ( spl55_21
  <=> v3_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_21])])).

fof(f6882,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl55_110 ),
    inference(avatar_component_clause,[],[f6881])).

fof(f6881,plain,
    ( spl55_110
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_110])])).

fof(f6883,plain,
    ( spl55_109
    | spl55_110 ),
    inference(avatar_split_clause,[],[f2005,f6881,f6878])).

fof(f6878,plain,
    ( spl55_109
  <=> ! [X1] :
        ( v3_ordinal1(X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_109])])).

fof(f2005,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(X1)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f1593,f1582])).

fof(f6876,plain,
    ( ~ spl55_107
    | spl55_108
    | ~ spl55_95 ),
    inference(avatar_split_clause,[],[f6576,f6001,f6873,f6869])).

fof(f6869,plain,
    ( spl55_107
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_107])])).

fof(f6873,plain,
    ( spl55_108
  <=> v1_relat_1(k1_tarski(k2_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_108])])).

fof(f6001,plain,
    ( spl55_95
  <=> r1_tarski(k1_tarski(k2_mcart_1(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_95])])).

fof(f6576,plain,
    ( v1_relat_1(k1_tarski(k2_mcart_1(sK3)))
    | ~ v1_relat_1(sK2)
    | ~ spl55_95 ),
    inference(resolution,[],[f2175,f6003])).

fof(f6003,plain,
    ( r1_tarski(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_95 ),
    inference(avatar_component_clause,[],[f6001])).

fof(f2175,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f1591,f1556])).

fof(f1556,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f6735,plain,
    ( ~ spl55_103
    | spl55_106
    | ~ spl55_52 ),
    inference(avatar_split_clause,[],[f6575,f4940,f6732,f6614])).

fof(f6614,plain,
    ( spl55_103
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_103])])).

fof(f6732,plain,
    ( spl55_106
  <=> v1_relat_1(k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_106])])).

fof(f4940,plain,
    ( spl55_52
  <=> r1_tarski(k2_tarski(sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_52])])).

fof(f6575,plain,
    ( v1_relat_1(k2_tarski(sK3,sK3))
    | ~ v1_relat_1(sK1)
    | ~ spl55_52 ),
    inference(resolution,[],[f2175,f4942])).

fof(f4942,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_52 ),
    inference(avatar_component_clause,[],[f4940])).

fof(f6645,plain,
    ( spl55_94
    | spl55_105 ),
    inference(avatar_split_clause,[],[f2295,f6643,f5964])).

fof(f6643,plain,
    ( spl55_105
  <=> ! [X14] : ~ r2_hidden(X14,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_105])])).

fof(f2295,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,k1_tarski(k1_xboole_0))
      | ~ v1_xboole_0(k1_zfmisc_1(X15)) ) ),
    inference(resolution,[],[f1551,f1596])).

fof(f1596,plain,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f631])).

fof(f631,axiom,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f6621,plain,
    ( ~ spl55_103
    | spl55_104
    | ~ spl55_44 ),
    inference(avatar_split_clause,[],[f6574,f3729,f6618,f6614])).

fof(f6618,plain,
    ( spl55_104
  <=> v1_relat_1(k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_104])])).

fof(f3729,plain,
    ( spl55_44
  <=> r1_tarski(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_44])])).

fof(f6574,plain,
    ( v1_relat_1(k1_tarski(sK3))
    | ~ v1_relat_1(sK1)
    | ~ spl55_44 ),
    inference(resolution,[],[f2175,f3731])).

fof(f3731,plain,
    ( r1_tarski(k1_tarski(sK3),sK1)
    | ~ spl55_44 ),
    inference(avatar_component_clause,[],[f3729])).

fof(f6511,plain,
    ( spl55_102
    | ~ spl55_19
    | ~ spl55_72 ),
    inference(avatar_split_clause,[],[f6368,f5530,f2043,f6508])).

fof(f6508,plain,
    ( spl55_102
  <=> v3_ordinal1(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_102])])).

fof(f5530,plain,
    ( spl55_72
  <=> r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_72])])).

fof(f6368,plain,
    ( v3_ordinal1(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))))
    | ~ spl55_19
    | ~ spl55_72 ),
    inference(subsumption_resolution,[],[f6357,f2045])).

fof(f2045,plain,
    ( v3_ordinal1(sK3)
    | ~ spl55_19 ),
    inference(avatar_component_clause,[],[f2043])).

fof(f6357,plain,
    ( v3_ordinal1(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))))
    | ~ v3_ordinal1(sK3)
    | ~ spl55_72 ),
    inference(resolution,[],[f2006,f5531])).

fof(f5531,plain,
    ( r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),sK3)
    | ~ spl55_72 ),
    inference(avatar_component_clause,[],[f5530])).

fof(f6381,plain,
    ( spl55_101
    | ~ spl55_19
    | ~ spl55_66 ),
    inference(avatar_split_clause,[],[f6367,f5480,f2043,f6378])).

fof(f6367,plain,
    ( v3_ordinal1(sK35(sK3,k2_mcart_1(sK3)))
    | ~ spl55_19
    | ~ spl55_66 ),
    inference(subsumption_resolution,[],[f6356,f2045])).

fof(f6356,plain,
    ( v3_ordinal1(sK35(sK3,k2_mcart_1(sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ spl55_66 ),
    inference(resolution,[],[f2006,f5481])).

fof(f6376,plain,
    ( spl55_99
    | spl55_100 ),
    inference(avatar_split_clause,[],[f2011,f6374,f6370])).

fof(f6370,plain,
    ( spl55_99
  <=> v3_ordinal1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_99])])).

fof(f6374,plain,
    ( spl55_100
  <=> ! [X9] : ~ v3_ordinal1(k1_zfmisc_1(k1_zfmisc_1(X9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_100])])).

fof(f2011,plain,(
    ! [X9] :
      ( ~ v3_ordinal1(k1_zfmisc_1(k1_zfmisc_1(X9)))
      | v3_ordinal1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f1593,f1596])).

fof(f6322,plain,
    ( spl55_98
    | spl55_2
    | ~ spl55_41 ),
    inference(avatar_split_clause,[],[f4663,f3490,f1899,f6319])).

fof(f6319,plain,
    ( spl55_98
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK36(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_98])])).

fof(f4663,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK36(sK1),sK3),sK1)
    | spl55_2
    | ~ spl55_41 ),
    inference(subsumption_resolution,[],[f4647,f1901])).

fof(f4647,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK36(sK1),sK3),sK1)
    | k1_xboole_0 = sK1
    | ~ spl55_41 ),
    inference(resolution,[],[f3550,f1680])).

fof(f1680,plain,(
    ! [X0] :
      ( r2_hidden(sK36(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1438])).

fof(f1438,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f6317,plain,
    ( spl55_97
    | spl55_93 ),
    inference(avatar_split_clause,[],[f2001,f5960,f6315])).

fof(f6315,plain,
    ( spl55_97
  <=> ! [X9] : ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_97])])).

fof(f5960,plain,
    ( spl55_93
  <=> v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_93])])).

fof(f2001,plain,(
    ! [X9] :
      ( v1_xboole_0(k1_tarski(k1_xboole_0))
      | ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X9))) ) ),
    inference(resolution,[],[f1583,f1596])).

fof(f6184,plain,
    ( spl55_96
    | ~ spl55_92 ),
    inference(avatar_split_clause,[],[f6124,f5945,f6181])).

fof(f6181,plain,
    ( spl55_96
  <=> sK2 = k2_xboole_0(sK2,k1_tarski(k2_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_96])])).

fof(f5945,plain,
    ( spl55_92
  <=> sK2 = k2_xboole_0(k1_tarski(k2_mcart_1(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_92])])).

fof(f6124,plain,
    ( sK2 = k2_xboole_0(sK2,k1_tarski(k2_mcart_1(sK3)))
    | ~ spl55_92 ),
    inference(superposition,[],[f5947,f1677])).

fof(f1677,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5947,plain,
    ( sK2 = k2_xboole_0(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_92 ),
    inference(avatar_component_clause,[],[f5945])).

fof(f6004,plain,
    ( spl55_95
    | ~ spl55_89 ),
    inference(avatar_split_clause,[],[f5974,f5931,f6001])).

fof(f5931,plain,
    ( spl55_89
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(k2_mcart_1(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_89])])).

fof(f5974,plain,
    ( r1_tarski(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_89 ),
    inference(trivial_inequality_removal,[],[f5973])).

fof(f5973,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_89 ),
    inference(superposition,[],[f1740,f5933])).

fof(f5933,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_89 ),
    inference(avatar_component_clause,[],[f5931])).

fof(f1740,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5966,plain,
    ( spl55_93
    | spl55_94 ),
    inference(avatar_split_clause,[],[f2195,f5964,f5960])).

fof(f2195,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(k1_zfmisc_1(X9))
      | v1_xboole_0(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f1592,f1596])).

fof(f1592,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1414])).

fof(f1414,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f541])).

fof(f541,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f5948,plain,
    ( spl55_92
    | ~ spl55_82 ),
    inference(avatar_split_clause,[],[f5792,f5771,f5945])).

fof(f5792,plain,
    ( sK2 = k2_xboole_0(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_82 ),
    inference(resolution,[],[f5773,f1674])).

fof(f1674,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f1436])).

fof(f1436,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f404])).

fof(f404,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f5942,plain,
    ( spl55_90
    | spl55_91 ),
    inference(avatar_split_clause,[],[f2180,f5940,f5936])).

fof(f5936,plain,
    ( spl55_90
  <=> v1_relat_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_90])])).

fof(f5940,plain,
    ( spl55_91
  <=> ! [X9] : ~ v1_relat_1(k1_zfmisc_1(X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_91])])).

fof(f2180,plain,(
    ! [X9] :
      ( ~ v1_relat_1(k1_zfmisc_1(X9))
      | v1_relat_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f1591,f1596])).

fof(f5934,plain,
    ( spl55_89
    | ~ spl55_82 ),
    inference(avatar_split_clause,[],[f5791,f5771,f5931])).

fof(f5791,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(k2_mcart_1(sK3)),sK2)
    | ~ spl55_82 ),
    inference(resolution,[],[f5773,f1732])).

fof(f1732,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f311])).

fof(f311,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f5874,plain,
    ( spl55_88
    | spl55_86
    | ~ spl55_70 ),
    inference(avatar_split_clause,[],[f5535,f5505,f5830,f5871])).

fof(f5830,plain,
    ( spl55_86
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_86])])).

fof(f5535,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),sK0)
    | ~ spl55_70 ),
    inference(resolution,[],[f5507,f1579])).

fof(f1579,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1406])).

fof(f1406,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f5863,plain,
    ( spl55_72
    | spl55_67
    | spl55_71 ),
    inference(avatar_split_clause,[],[f5542,f5526,f5485,f5530])).

fof(f5526,plain,
    ( spl55_71
  <=> r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),k1_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_71])])).

fof(f5542,plain,
    ( r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),sK3)
    | spl55_67
    | spl55_71 ),
    inference(subsumption_resolution,[],[f5538,f5487])).

fof(f5487,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK3))
    | spl55_67 ),
    inference(avatar_component_clause,[],[f5485])).

fof(f5538,plain,
    ( r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_71 ),
    inference(resolution,[],[f5528,f1667])).

fof(f5528,plain,
    ( ~ r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),k1_mcart_1(k1_mcart_1(sK3)))
    | spl55_71 ),
    inference(avatar_component_clause,[],[f5526])).

fof(f5837,plain,
    ( ~ spl55_86
    | spl55_87
    | ~ spl55_70 ),
    inference(avatar_split_clause,[],[f5537,f5505,f5834,f5830])).

fof(f5834,plain,
    ( spl55_87
  <=> v1_xboole_0(k1_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_87])])).

fof(f5537,plain,
    ( v1_xboole_0(k1_mcart_1(k1_mcart_1(sK3)))
    | ~ v1_xboole_0(sK0)
    | ~ spl55_70 ),
    inference(resolution,[],[f5507,f1583])).

fof(f5824,plain,
    ( spl55_84
    | ~ spl55_85
    | ~ spl55_70 ),
    inference(avatar_split_clause,[],[f5536,f5505,f5821,f5817])).

fof(f5817,plain,
    ( spl55_84
  <=> v3_ordinal1(k1_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_84])])).

fof(f5821,plain,
    ( spl55_85
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_85])])).

fof(f5536,plain,
    ( ~ v3_ordinal1(sK0)
    | v3_ordinal1(k1_mcart_1(k1_mcart_1(sK3)))
    | ~ spl55_70 ),
    inference(resolution,[],[f5507,f1593])).

fof(f5789,plain,
    ( spl55_83
    | ~ spl55_12 ),
    inference(avatar_split_clause,[],[f1978,f1949,f5786])).

fof(f5786,plain,
    ( spl55_83
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_83])])).

fof(f1949,plain,
    ( spl55_12
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_12])])).

fof(f1978,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl55_12 ),
    inference(superposition,[],[f1596,f1951])).

fof(f1951,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl55_12 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f5774,plain,
    ( spl55_82
    | spl55_78
    | ~ spl55_62 ),
    inference(avatar_split_clause,[],[f5431,f5405,f5684,f5771])).

fof(f5684,plain,
    ( spl55_78
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_78])])).

fof(f5431,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(k2_mcart_1(sK3),sK2)
    | ~ spl55_62 ),
    inference(resolution,[],[f5407,f1579])).

fof(f5750,plain,
    ( spl55_66
    | spl55_60
    | spl55_65 ),
    inference(avatar_split_clause,[],[f5494,f5476,f5363,f5480])).

fof(f5494,plain,
    ( r2_hidden(sK35(sK3,k2_mcart_1(sK3)),sK3)
    | spl55_60
    | spl55_65 ),
    inference(subsumption_resolution,[],[f5490,f5365])).

fof(f5365,plain,
    ( sK3 != k2_mcart_1(sK3)
    | spl55_60 ),
    inference(avatar_component_clause,[],[f5363])).

fof(f5490,plain,
    ( r2_hidden(sK35(sK3,k2_mcart_1(sK3)),sK3)
    | sK3 = k2_mcart_1(sK3)
    | spl55_65 ),
    inference(resolution,[],[f5478,f1667])).

fof(f5749,plain,
    ( spl55_80
    | spl55_81 ),
    inference(avatar_split_clause,[],[f2293,f5747,f5744])).

fof(f5744,plain,
    ( spl55_80
  <=> ! [X10] : ~ v1_xboole_0(X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_80])])).

fof(f5747,plain,
    ( spl55_81
  <=> ! [X9] : ~ r2_hidden(X9,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_81])])).

fof(f2293,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ v1_xboole_0(X10) ) ),
    inference(resolution,[],[f1551,f1597])).

fof(f1597,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f5691,plain,
    ( ~ spl55_78
    | spl55_79
    | ~ spl55_62 ),
    inference(avatar_split_clause,[],[f5433,f5405,f5688,f5684])).

fof(f5688,plain,
    ( spl55_79
  <=> v1_xboole_0(k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_79])])).

fof(f5433,plain,
    ( v1_xboole_0(k2_mcart_1(sK3))
    | ~ v1_xboole_0(sK2)
    | ~ spl55_62 ),
    inference(resolution,[],[f5407,f1583])).

fof(f5573,plain,
    ( spl55_77
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f5222,f1909,f1904,f1899,f1894,f5570])).

fof(f5570,plain,
    ( spl55_77
  <=> sK3 = k3_mcart_1(sK26(sK0,sK1,sK2,sK3),sK27(sK0,sK1,sK2,sK3),sK28(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_77])])).

fof(f5222,plain,
    ( sK3 = k3_mcart_1(sK26(sK0,sK1,sK2,sK3),sK27(sK0,sK1,sK2,sK3),sK28(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f5221,f1896])).

fof(f5221,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(sK26(sK0,sK1,sK2,sK3),sK27(sK0,sK1,sK2,sK3),sK28(sK0,sK1,sK2,sK3))
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f5220,f1906])).

fof(f5220,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(sK26(sK0,sK1,sK2,sK3),sK27(sK0,sK1,sK2,sK3),sK28(sK0,sK1,sK2,sK3))
    | spl55_2
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f5207,f1901])).

fof(f5207,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(sK26(sK0,sK1,sK2,sK3),sK27(sK0,sK1,sK2,sK3),sK28(sK0,sK1,sK2,sK3))
    | ~ spl55_4 ),
    inference(resolution,[],[f1612,f1911])).

fof(f1612,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(sK26(X0,X1,X2,X3),sK27(X0,X1,X2,X3),sK28(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f1421])).

fof(f1421,plain,(
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
    inference(ennf_transformation,[],[f1289])).

fof(f1289,axiom,(
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

fof(f5565,plain,
    ( spl55_67
    | spl55_73
    | spl55_74 ),
    inference(avatar_contradiction_clause,[],[f5564])).

fof(f5564,plain,
    ( $false
    | spl55_67
    | spl55_73
    | spl55_74 ),
    inference(subsumption_resolution,[],[f5563,f5487])).

fof(f5563,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_73
    | spl55_74 ),
    inference(subsumption_resolution,[],[f5562,f5546])).

fof(f5546,plain,
    ( ~ r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | spl55_73 ),
    inference(avatar_component_clause,[],[f5544])).

fof(f5544,plain,
    ( spl55_73
  <=> r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_73])])).

fof(f5562,plain,
    ( r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_74 ),
    inference(resolution,[],[f5550,f1667])).

fof(f5550,plain,
    ( ~ r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),k1_mcart_1(k1_mcart_1(sK3)))
    | spl55_74 ),
    inference(avatar_component_clause,[],[f5548])).

fof(f5548,plain,
    ( spl55_74
  <=> r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),k1_mcart_1(k1_mcart_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_74])])).

fof(f5561,plain,
    ( spl55_75
    | ~ spl55_76
    | ~ spl55_62 ),
    inference(avatar_split_clause,[],[f5432,f5405,f5558,f5554])).

fof(f5558,plain,
    ( spl55_76
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_76])])).

fof(f5432,plain,
    ( ~ v3_ordinal1(sK2)
    | v3_ordinal1(k2_mcart_1(sK3))
    | ~ spl55_62 ),
    inference(resolution,[],[f5407,f1593])).

fof(f5551,plain,
    ( ~ spl55_73
    | ~ spl55_74
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(avatar_split_clause,[],[f4932,f1967,f1909,f1904,f1899,f1894,f5548,f5544])).

fof(f4932,plain,
    ( ~ r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),k1_mcart_1(k1_mcart_1(sK3)))
    | ~ r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(forward_demodulation,[],[f4929,f4926])).

fof(f4926,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4925,f1896])).

fof(f4925,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4924,f1906])).

fof(f4924,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_2
    | ~ spl55_4 ),
    inference(subsumption_resolution,[],[f4911,f1901])).

fof(f4911,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl55_4 ),
    inference(resolution,[],[f1527,f1911])).

fof(f1527,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f1358])).

fof(f4929,plain,
    ( ~ r2_hidden(sK35(k1_mcart_1(k1_mcart_1(sK3)),sK3),sK3)
    | ~ r2_hidden(sK35(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k5_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(backward_demodulation,[],[f3331,f4926])).

fof(f3331,plain,
    ( ~ r2_hidden(sK35(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3)
    | ~ r2_hidden(sK35(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k5_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_15 ),
    inference(extensionality_resolution,[],[f1668,f1968])).

fof(f1968,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK3)
    | spl55_15 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f5541,plain,
    ( spl55_67
    | spl55_71
    | spl55_72 ),
    inference(avatar_contradiction_clause,[],[f5540])).

fof(f5540,plain,
    ( $false
    | spl55_67
    | spl55_71
    | spl55_72 ),
    inference(subsumption_resolution,[],[f5539,f5487])).

fof(f5539,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | spl55_71
    | spl55_72 ),
    inference(subsumption_resolution,[],[f5538,f5532])).

fof(f5532,plain,
    ( ~ r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),sK3)
    | spl55_72 ),
    inference(avatar_component_clause,[],[f5530])).

fof(f5533,plain,
    ( ~ spl55_71
    | ~ spl55_72
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(avatar_split_clause,[],[f4931,f1967,f1909,f1904,f1899,f1894,f5530,f5526])).

fof(f4931,plain,
    ( ~ r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),sK3)
    | ~ r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),k1_mcart_1(k1_mcart_1(sK3)))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(forward_demodulation,[],[f4928,f4926])).

fof(f4928,plain,
    ( ~ r2_hidden(sK35(sK3,k1_mcart_1(k1_mcart_1(sK3))),k1_mcart_1(k1_mcart_1(sK3)))
    | ~ r2_hidden(sK35(sK3,k5_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(backward_demodulation,[],[f3330,f4926])).

fof(f3330,plain,
    ( ~ r2_hidden(sK35(sK3,k5_mcart_1(sK0,sK1,sK2,sK3)),k5_mcart_1(sK0,sK1,sK2,sK3))
    | ~ r2_hidden(sK35(sK3,k5_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | spl55_15 ),
    inference(extensionality_resolution,[],[f1668,f1968])).

fof(f5513,plain,
    ( spl55_60
    | spl55_68
    | spl55_69 ),
    inference(avatar_contradiction_clause,[],[f5512])).

fof(f5512,plain,
    ( $false
    | spl55_60
    | spl55_68
    | spl55_69 ),
    inference(subsumption_resolution,[],[f5511,f5365])).

fof(f5508,plain,
    ( spl55_70
    | ~ spl55_4
    | ~ spl55_59 ),
    inference(avatar_split_clause,[],[f5374,f5358,f1909,f5505])).

fof(f5374,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK3)),sK0)
    | ~ spl55_4
    | ~ spl55_59 ),
    inference(subsumption_resolution,[],[f5373,f1911])).

fof(f5373,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK3)),sK0)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_59 ),
    inference(superposition,[],[f1535,f5360])).

fof(f1535,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f1362])).

fof(f1362,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f5503,plain,
    ( ~ spl55_68
    | ~ spl55_69
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(avatar_split_clause,[],[f4740,f1959,f1909,f1904,f1899,f1894,f5500,f5496])).

fof(f4740,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(sK3),sK3),k2_mcart_1(sK3))
    | ~ r2_hidden(sK35(k2_mcart_1(sK3),sK3),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(forward_demodulation,[],[f4737,f4734])).

fof(f4737,plain,
    ( ~ r2_hidden(sK35(k2_mcart_1(sK3),sK3),sK3)
    | ~ r2_hidden(sK35(k7_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(backward_demodulation,[],[f3329,f4734])).

fof(f3329,plain,
    ( ~ r2_hidden(sK35(k7_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3)
    | ~ r2_hidden(sK35(k7_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_13 ),
    inference(extensionality_resolution,[],[f1668,f1960])).

fof(f1960,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK3)
    | spl55_13 ),
    inference(avatar_component_clause,[],[f1959])).

fof(f5493,plain,
    ( spl55_60
    | spl55_65
    | spl55_66 ),
    inference(avatar_contradiction_clause,[],[f5492])).

fof(f5492,plain,
    ( $false
    | spl55_60
    | spl55_65
    | spl55_66 ),
    inference(subsumption_resolution,[],[f5491,f5365])).

% (23140)lrs+1002_3:1_av=off:bd=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:lma=on:lwlo=on:nm=4:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_134 on theBenchmark
fof(f5491,plain,
    ( sK3 = k2_mcart_1(sK3)
    | spl55_65
    | spl55_66 ),
    inference(subsumption_resolution,[],[f5490,f5482])).

fof(f5482,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(sK3)),sK3)
    | spl55_66 ),
    inference(avatar_component_clause,[],[f5480])).

fof(f5488,plain,
    ( ~ spl55_67
    | spl55_15
    | ~ spl55_59 ),
    inference(avatar_split_clause,[],[f5372,f5358,f1967,f5485])).

fof(f5372,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK3))
    | spl55_15
    | ~ spl55_59 ),
    inference(superposition,[],[f1968,f5360])).

fof(f5483,plain,
    ( ~ spl55_65
    | ~ spl55_66
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(avatar_split_clause,[],[f4739,f1959,f1909,f1904,f1899,f1894,f5480,f5476])).

fof(f4739,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(sK3)),sK3)
    | ~ r2_hidden(sK35(sK3,k2_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(forward_demodulation,[],[f4736,f4734])).

fof(f4736,plain,
    ( ~ r2_hidden(sK35(sK3,k2_mcart_1(sK3)),k2_mcart_1(sK3))
    | ~ r2_hidden(sK35(sK3,k7_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(backward_demodulation,[],[f3328,f4734])).

fof(f3328,plain,
    ( ~ r2_hidden(sK35(sK3,k7_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ r2_hidden(sK35(sK3,k7_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | spl55_13 ),
    inference(extensionality_resolution,[],[f1668,f1960])).

fof(f5422,plain,
    ( spl55_23
    | spl55_17
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f2170,f1909,f2020,f2186])).

fof(f2186,plain,
    ( spl55_23
  <=> r2_hidden(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_23])])).

fof(f2020,plain,
    ( spl55_17
  <=> v1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_17])])).

fof(f2170,plain,
    ( v1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2))
    | r2_hidden(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_4 ),
    inference(resolution,[],[f1579,f1911])).

fof(f5417,plain,
    ( ~ spl55_63
    | ~ spl55_64
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(avatar_split_clause,[],[f4930,f1967,f1909,f1904,f1899,f1894,f5414,f5410])).

fof(f4930,plain,
    ( ~ r1_tarski(sK3,k1_mcart_1(k1_mcart_1(sK3)))
    | ~ r1_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(forward_demodulation,[],[f4927,f4926])).

fof(f4927,plain,
    ( ~ r1_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)
    | ~ r1_tarski(sK3,k5_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_15 ),
    inference(backward_demodulation,[],[f2890,f4926])).

fof(f2890,plain,
    ( ~ r1_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k5_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_15 ),
    inference(extensionality_resolution,[],[f1666,f1968])).

fof(f5408,plain,
    ( spl55_62
    | ~ spl55_4
    | ~ spl55_56 ),
    inference(avatar_split_clause,[],[f5356,f5341,f1909,f5405])).

fof(f5356,plain,
    ( m1_subset_1(k2_mcart_1(sK3),sK2)
    | ~ spl55_4
    | ~ spl55_56 ),
    inference(subsumption_resolution,[],[f5355,f1911])).

fof(f5355,plain,
    ( m1_subset_1(k2_mcart_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_56 ),
    inference(superposition,[],[f1520,f5343])).

fof(f1520,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f1355])).

fof(f1355,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1287])).

fof(f1287,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f5371,plain,
    ( spl55_61
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(avatar_split_clause,[],[f5195,f1963,f1909,f1904,f1899,f1894,f5368])).

fof(f5195,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(forward_demodulation,[],[f5194,f4926])).

fof(f5194,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(forward_demodulation,[],[f5193,f1965])).

fof(f1965,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl55_14 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f5366,plain,
    ( ~ spl55_60
    | spl55_13
    | ~ spl55_56 ),
    inference(avatar_split_clause,[],[f5354,f5341,f1959,f5363])).

fof(f5354,plain,
    ( sK3 != k2_mcart_1(sK3)
    | spl55_13
    | ~ spl55_56 ),
    inference(superposition,[],[f1960,f5343])).

fof(f5361,plain,
    ( spl55_59
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f4926,f1909,f1904,f1899,f1894,f5358])).

fof(f5353,plain,
    ( ~ spl55_57
    | ~ spl55_58
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(avatar_split_clause,[],[f4738,f1959,f1909,f1904,f1899,f1894,f5350,f5346])).

fof(f4738,plain,
    ( ~ r1_tarski(sK3,k2_mcart_1(sK3))
    | ~ r1_tarski(k2_mcart_1(sK3),sK3)
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(forward_demodulation,[],[f4735,f4734])).

fof(f4735,plain,
    ( ~ r1_tarski(k2_mcart_1(sK3),sK3)
    | ~ r1_tarski(sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | spl55_13 ),
    inference(backward_demodulation,[],[f2335,f4734])).

fof(f2335,plain,
    ( ~ r1_tarski(k7_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl55_13 ),
    inference(extensionality_resolution,[],[f1666,f1960])).

fof(f5344,plain,
    ( spl55_56
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f4734,f1909,f1904,f1899,f1894,f5341])).

fof(f5339,plain,
    ( spl55_55
    | ~ spl55_54 ),
    inference(avatar_split_clause,[],[f5229,f5147,f5336])).

fof(f5336,plain,
    ( spl55_55
  <=> sK1 = k2_xboole_0(sK1,k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_55])])).

fof(f5147,plain,
    ( spl55_54
  <=> sK1 = k2_xboole_0(k2_tarski(sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_54])])).

fof(f5229,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tarski(sK3,sK3))
    | ~ spl55_54 ),
    inference(superposition,[],[f5149,f1677])).

fof(f5149,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_54 ),
    inference(avatar_component_clause,[],[f5147])).

fof(f5150,plain,
    ( spl55_54
    | ~ spl55_52 ),
    inference(avatar_split_clause,[],[f5061,f4940,f5147])).

fof(f5061,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_52 ),
    inference(resolution,[],[f4942,f1673])).

fof(f1673,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1435,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f5022,plain,
    ( spl55_53
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(avatar_split_clause,[],[f4965,f1963,f1909,f1904,f1899,f1894,f5019])).

fof(f4965,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | spl55_1
    | spl55_2
    | spl55_3
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(forward_demodulation,[],[f4964,f1965])).

fof(f4943,plain,
    ( spl55_52
    | ~ spl55_51 ),
    inference(avatar_split_clause,[],[f4824,f4748,f4940])).

fof(f4748,plain,
    ( spl55_51
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_51])])).

fof(f4824,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_51 ),
    inference(trivial_inequality_removal,[],[f4823])).

fof(f4823,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_51 ),
    inference(superposition,[],[f1740,f4750])).

fof(f4750,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_51 ),
    inference(avatar_component_clause,[],[f4748])).

fof(f4751,plain,
    ( spl55_51
    | ~ spl55_41 ),
    inference(avatar_split_clause,[],[f4638,f3490,f4748])).

fof(f4638,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK3,sK3),sK1)
    | ~ spl55_41 ),
    inference(resolution,[],[f3550,f3492])).

fof(f4452,plain,
    ( spl55_50
    | ~ spl55_23 ),
    inference(avatar_split_clause,[],[f2961,f2186,f4449])).

fof(f4449,plain,
    ( spl55_50
  <=> k1_xboole_0 = k1_funct_1(sK43(k3_zfmisc_1(sK0,sK1,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_50])])).

fof(f2961,plain,
    ( k1_xboole_0 = k1_funct_1(sK43(k3_zfmisc_1(sK0,sK1,sK2)),sK3)
    | ~ spl55_23 ),
    inference(resolution,[],[f2188,f1776])).

fof(f1776,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK43(X0),X2) ) ),
    inference(cnf_transformation,[],[f1480])).

fof(f1480,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f941])).

fof(f941,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f2188,plain,
    ( r2_hidden(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_23 ),
    inference(avatar_component_clause,[],[f2186])).

fof(f4380,plain,
    ( spl55_49
    | ~ spl55_23 ),
    inference(avatar_split_clause,[],[f2960,f2186,f4377])).

fof(f4377,plain,
    ( spl55_49
  <=> k1_xboole_0 = k1_funct_1(sK44(k3_zfmisc_1(sK0,sK1,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_49])])).

fof(f2960,plain,
    ( k1_xboole_0 = k1_funct_1(sK44(k3_zfmisc_1(sK0,sK1,sK2)),sK3)
    | ~ spl55_23 ),
    inference(resolution,[],[f2188,f1780])).

fof(f1780,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK44(X0),X2) ) ),
    inference(cnf_transformation,[],[f1481])).

fof(f1481,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f944])).

fof(f944,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(f4226,plain,
    ( spl55_46
    | ~ spl55_48
    | ~ spl55_44 ),
    inference(avatar_split_clause,[],[f3797,f3729,f4223,f4145])).

fof(f4145,plain,
    ( spl55_46
  <=> sK1 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_46])])).

fof(f4223,plain,
    ( spl55_48
  <=> r1_tarski(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_48])])).

fof(f3797,plain,
    ( ~ r1_tarski(sK1,k1_tarski(sK3))
    | sK1 = k1_tarski(sK3)
    | ~ spl55_44 ),
    inference(resolution,[],[f3731,f1666])).

fof(f4151,plain,
    ( spl55_46
    | spl55_47
    | spl55_2
    | ~ spl55_43 ),
    inference(avatar_split_clause,[],[f3861,f3629,f1899,f4149,f4145])).

fof(f4149,plain,
    ( spl55_47
  <=> ! [X3] : k1_tarski(X3) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_47])])).

fof(f3629,plain,
    ( spl55_43
  <=> sK1 = k2_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_43])])).

fof(f3861,plain,
    ( ! [X3] :
        ( k1_tarski(X3) != sK1
        | sK1 = k1_tarski(sK3) )
    | spl55_2
    | ~ spl55_43 ),
    inference(subsumption_resolution,[],[f3860,f1901])).

fof(f3860,plain,
    ( ! [X3] :
        ( k1_tarski(X3) != sK1
        | sK1 = k1_tarski(sK3)
        | k1_xboole_0 = sK1 )
    | ~ spl55_43 ),
    inference(subsumption_resolution,[],[f3847,f1979])).

fof(f3847,plain,
    ( ! [X3] :
        ( k1_tarski(X3) != sK1
        | sK1 = k1_tarski(sK3)
        | k1_xboole_0 = k1_tarski(sK3)
        | k1_xboole_0 = sK1 )
    | ~ spl55_43 ),
    inference(superposition,[],[f1634,f3631])).

fof(f3631,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl55_43 ),
    inference(avatar_component_clause,[],[f3629])).

fof(f1634,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k1_tarski(X0)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f1425])).

fof(f1425,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f402])).

fof(f402,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f3890,plain,
    ( spl55_45
    | ~ spl55_43 ),
    inference(avatar_split_clause,[],[f3841,f3629,f3887])).

fof(f3887,plain,
    ( spl55_45
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_45])])).

fof(f3841,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl55_43 ),
    inference(superposition,[],[f3631,f1677])).

fof(f3732,plain,
    ( spl55_44
    | ~ spl55_42 ),
    inference(avatar_split_clause,[],[f3665,f3589,f3729])).

fof(f3589,plain,
    ( spl55_42
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_42])])).

fof(f3665,plain,
    ( r1_tarski(k1_tarski(sK3),sK1)
    | ~ spl55_42 ),
    inference(trivial_inequality_removal,[],[f3664])).

fof(f3664,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK3),sK1)
    | ~ spl55_42 ),
    inference(superposition,[],[f1740,f3591])).

fof(f3591,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl55_42 ),
    inference(avatar_component_clause,[],[f3589])).

fof(f3632,plain,
    ( spl55_43
    | ~ spl55_41 ),
    inference(avatar_split_clause,[],[f3552,f3490,f3629])).

fof(f3552,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl55_41 ),
    inference(resolution,[],[f3492,f1674])).

fof(f3592,plain,
    ( spl55_42
    | ~ spl55_41 ),
    inference(avatar_split_clause,[],[f3551,f3490,f3589])).

fof(f3551,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl55_41 ),
    inference(resolution,[],[f3492,f1732])).

fof(f3493,plain,
    ( spl55_41
    | spl55_40
    | ~ spl55_39 ),
    inference(avatar_split_clause,[],[f3256,f3211,f3364,f3490])).

fof(f3364,plain,
    ( spl55_40
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_40])])).

fof(f3211,plain,
    ( spl55_39
  <=> m1_subset_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_39])])).

fof(f3256,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK3,sK1)
    | ~ spl55_39 ),
    inference(resolution,[],[f3213,f1579])).

fof(f3213,plain,
    ( m1_subset_1(sK3,sK1)
    | ~ spl55_39 ),
    inference(avatar_component_clause,[],[f3211])).

fof(f3367,plain,
    ( ~ spl55_40
    | spl55_18
    | ~ spl55_39 ),
    inference(avatar_split_clause,[],[f3259,f3211,f2024,f3364])).

fof(f2024,plain,
    ( spl55_18
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_18])])).

fof(f3259,plain,
    ( ~ v1_xboole_0(sK1)
    | spl55_18
    | ~ spl55_39 ),
    inference(subsumption_resolution,[],[f3258,f2025])).

fof(f2025,plain,
    ( ~ v1_xboole_0(sK3)
    | spl55_18 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f3258,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1)
    | ~ spl55_39 ),
    inference(resolution,[],[f3213,f1583])).

fof(f3214,plain,
    ( spl55_39
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(avatar_split_clause,[],[f3185,f1963,f1909,f3211])).

fof(f3185,plain,
    ( m1_subset_1(sK3,sK1)
    | ~ spl55_4
    | ~ spl55_14 ),
    inference(subsumption_resolution,[],[f3184,f1911])).

fof(f3184,plain,
    ( m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_14 ),
    inference(superposition,[],[f1531,f1965])).

fof(f1531,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f1360])).

fof(f1360,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f3103,plain,
    ( ~ spl55_38
    | spl55_35 ),
    inference(avatar_split_clause,[],[f2894,f2877,f3100])).

fof(f3100,plain,
    ( spl55_38
  <=> r1_tarski(k5_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_38])])).

fof(f2877,plain,
    ( spl55_35
  <=> k1_xboole_0 = k5_mcart_1(sK0,sK1,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_35])])).

fof(f2894,plain,
    ( ~ r1_tarski(k5_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0)
    | spl55_35 ),
    inference(subsumption_resolution,[],[f2892,f1834])).

fof(f1834,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2892,plain,
    ( ~ r1_tarski(k5_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_mcart_1(sK0,sK1,sK2,k1_xboole_0))
    | spl55_35 ),
    inference(extensionality_resolution,[],[f1666,f2878])).

fof(f2878,plain,
    ( k1_xboole_0 != k5_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | spl55_35 ),
    inference(avatar_component_clause,[],[f2877])).

fof(f3081,plain,
    ( ~ spl55_37
    | spl55_33 ),
    inference(avatar_split_clause,[],[f2882,f2849,f3078])).

fof(f3078,plain,
    ( spl55_37
  <=> r1_tarski(k7_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_37])])).

fof(f2849,plain,
    ( spl55_33
  <=> k1_xboole_0 = k7_mcart_1(sK0,sK1,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_33])])).

fof(f2882,plain,
    ( ~ r1_tarski(k7_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0)
    | spl55_33 ),
    inference(subsumption_resolution,[],[f2872,f1834])).

fof(f2872,plain,
    ( ~ r1_tarski(k1_xboole_0,k7_mcart_1(sK0,sK1,sK2,k1_xboole_0))
    | ~ r1_tarski(k7_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0)
    | spl55_33 ),
    inference(extensionality_resolution,[],[f1666,f2851])).

fof(f2851,plain,
    ( k1_xboole_0 != k7_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | spl55_33 ),
    inference(avatar_component_clause,[],[f2849])).

fof(f3052,plain,
    ( ~ spl55_36
    | spl55_34 ),
    inference(avatar_split_clause,[],[f2875,f2854,f3049])).

fof(f3049,plain,
    ( spl55_36
  <=> r1_tarski(k6_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_36])])).

fof(f2854,plain,
    ( spl55_34
  <=> k1_xboole_0 = k6_mcart_1(sK0,sK1,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_34])])).

fof(f2875,plain,
    ( ~ r1_tarski(k6_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0)
    | spl55_34 ),
    inference(subsumption_resolution,[],[f2873,f1834])).

fof(f2873,plain,
    ( ~ r1_tarski(k6_mcart_1(sK0,sK1,sK2,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_mcart_1(sK0,sK1,sK2,k1_xboole_0))
    | spl55_34 ),
    inference(extensionality_resolution,[],[f1666,f2855])).

fof(f2855,plain,
    ( k1_xboole_0 != k6_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | spl55_34 ),
    inference(avatar_component_clause,[],[f2854])).

fof(f3015,plain,
    ( ~ spl55_17
    | spl55_18
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f2600,f1909,f2024,f2020])).

fof(f2600,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_4 ),
    inference(resolution,[],[f1911,f1583])).

fof(f2924,plain,
    ( spl55_23
    | ~ spl55_29 ),
    inference(avatar_split_clause,[],[f2808,f2534,f2186])).

fof(f2534,plain,
    ( spl55_29
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_29])])).

fof(f2808,plain,
    ( r2_hidden(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_29 ),
    inference(trivial_inequality_removal,[],[f2804])).

fof(f2804,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_29 ),
    inference(superposition,[],[f1733,f2536])).

fof(f2536,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_29 ),
    inference(avatar_component_clause,[],[f2534])).

fof(f1733,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f311])).

fof(f2880,plain,
    ( spl55_35
    | ~ spl55_15
    | ~ spl55_18 ),
    inference(avatar_split_clause,[],[f2862,f2024,f1967,f2877])).

fof(f2862,plain,
    ( k1_xboole_0 = k5_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl55_15
    | ~ spl55_18 ),
    inference(backward_demodulation,[],[f1969,f2858])).

fof(f2858,plain,
    ( k1_xboole_0 = sK3
    | ~ spl55_18 ),
    inference(resolution,[],[f2026,f1822])).

fof(f1822,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1512])).

fof(f1512,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2026,plain,
    ( v1_xboole_0(sK3)
    | ~ spl55_18 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f1969,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl55_15 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f2857,plain,
    ( spl55_34
    | ~ spl55_14
    | ~ spl55_18 ),
    inference(avatar_split_clause,[],[f2577,f2024,f1963,f2854])).

fof(f2577,plain,
    ( k1_xboole_0 = k6_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl55_14
    | ~ spl55_18 ),
    inference(backward_demodulation,[],[f1965,f2574])).

fof(f2574,plain,
    ( k1_xboole_0 = sK3
    | ~ spl55_18 ),
    inference(resolution,[],[f2026,f1822])).

fof(f2852,plain,
    ( ~ spl55_33
    | spl55_13
    | ~ spl55_18 ),
    inference(avatar_split_clause,[],[f2576,f2024,f1959,f2849])).

fof(f2576,plain,
    ( k1_xboole_0 != k7_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | spl55_13
    | ~ spl55_18 ),
    inference(backward_demodulation,[],[f1960,f2574])).

fof(f2844,plain,
    ( spl55_32
    | ~ spl55_29 ),
    inference(avatar_split_clause,[],[f2807,f2534,f2841])).

fof(f2841,plain,
    ( spl55_32
  <=> r1_tarski(k1_tarski(sK3),k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_32])])).

fof(f2807,plain,
    ( r1_tarski(k1_tarski(sK3),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_29 ),
    inference(trivial_inequality_removal,[],[f2806])).

fof(f2806,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK3),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_29 ),
    inference(superposition,[],[f1740,f2536])).

fof(f2715,plain,
    ( ~ spl55_31
    | spl55_30 ),
    inference(avatar_split_clause,[],[f2602,f2594,f2712])).

fof(f2712,plain,
    ( spl55_31
  <=> r2_hidden(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_31])])).

fof(f2594,plain,
    ( spl55_30
  <=> m1_subset_1(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_30])])).

fof(f2602,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | spl55_30 ),
    inference(resolution,[],[f2595,f1575])).

fof(f2595,plain,
    ( ~ m1_subset_1(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | spl55_30 ),
    inference(avatar_component_clause,[],[f2594])).

fof(f2597,plain,
    ( spl55_30
    | ~ spl55_4
    | ~ spl55_18 ),
    inference(avatar_split_clause,[],[f2575,f2024,f1909,f2594])).

fof(f2575,plain,
    ( m1_subset_1(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_4
    | ~ spl55_18 ),
    inference(backward_demodulation,[],[f1911,f2574])).

fof(f2587,plain,
    ( ~ spl55_18
    | spl55_19
    | ~ spl55_21 ),
    inference(avatar_contradiction_clause,[],[f2586])).

fof(f2586,plain,
    ( $false
    | ~ spl55_18
    | spl55_19
    | ~ spl55_21 ),
    inference(subsumption_resolution,[],[f2580,f2124])).

fof(f2580,plain,
    ( ~ v3_ordinal1(k1_xboole_0)
    | ~ spl55_18
    | spl55_19 ),
    inference(backward_demodulation,[],[f2044,f2574])).

fof(f2044,plain,
    ( ~ v3_ordinal1(sK3)
    | spl55_19 ),
    inference(avatar_component_clause,[],[f2043])).

fof(f2537,plain,
    ( spl55_29
    | ~ spl55_23 ),
    inference(avatar_split_clause,[],[f2404,f2186,f2534])).

fof(f2404,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_23 ),
    inference(resolution,[],[f1732,f2188])).

fof(f2504,plain,(
    spl55_28 ),
    inference(avatar_split_clause,[],[f2479,f2501])).

fof(f2501,plain,
    ( spl55_28
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_28])])).

fof(f2479,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1882,f2476])).

fof(f2476,plain,(
    ! [X2] : k1_xboole_0 = sK39(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2474,f1883])).

fof(f1883,plain,(
    ! [X0] : v1_relat_1(sK39(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f1721])).

fof(f1721,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | v1_relat_1(sK39(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1459,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1458])).

fof(f1458,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1001])).

fof(f1001,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f2474,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK39(X2,k1_xboole_0))
      | k1_xboole_0 = sK39(X2,k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f2467])).

fof(f2467,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ v1_relat_1(sK39(X2,k1_xboole_0))
      | k1_xboole_0 = sK39(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f1814,f1881])).

fof(f1881,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK39(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f1723])).

fof(f1723,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_relat_1(sK39(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1814,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1506])).

fof(f1506,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1505])).

fof(f1505,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f859])).

fof(f859,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1882,plain,(
    ! [X0] : v1_funct_1(sK39(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f1722])).

fof(f1722,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | v1_funct_1(sK39(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f2427,plain,
    ( ~ spl55_27
    | spl55_3 ),
    inference(avatar_split_clause,[],[f2360,f1904,f2424])).

fof(f2424,plain,
    ( spl55_27
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_27])])).

fof(f2360,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl55_3 ),
    inference(subsumption_resolution,[],[f2333,f1834])).

fof(f2333,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | spl55_3 ),
    inference(extensionality_resolution,[],[f1666,f1906])).

fof(f2395,plain,
    ( ~ spl55_26
    | spl55_2 ),
    inference(avatar_split_clause,[],[f2359,f1899,f2392])).

fof(f2392,plain,
    ( spl55_26
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_26])])).

fof(f2359,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl55_2 ),
    inference(subsumption_resolution,[],[f2331,f1834])).

fof(f2331,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | spl55_2 ),
    inference(extensionality_resolution,[],[f1666,f1901])).

fof(f2365,plain,
    ( ~ spl55_25
    | spl55_1 ),
    inference(avatar_split_clause,[],[f2358,f1894,f2362])).

fof(f2362,plain,
    ( spl55_25
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_25])])).

fof(f2358,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl55_1 ),
    inference(subsumption_resolution,[],[f2329,f1834])).

fof(f2329,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | spl55_1 ),
    inference(extensionality_resolution,[],[f1666,f1896])).

fof(f2221,plain,(
    spl55_24 ),
    inference(avatar_split_clause,[],[f2149,f2218])).

fof(f2218,plain,
    ( spl55_24
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_24])])).

fof(f2149,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f1554,f1586])).

fof(f1586,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

fof(f1554,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1382])).

fof(f1382,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2189,plain,
    ( spl55_23
    | ~ spl55_4
    | spl55_17 ),
    inference(avatar_split_clause,[],[f2173,f2020,f1909,f2186])).

fof(f2173,plain,
    ( r2_hidden(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_4
    | spl55_17 ),
    inference(subsumption_resolution,[],[f2170,f2022])).

fof(f2022,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2))
    | spl55_17 ),
    inference(avatar_component_clause,[],[f2020])).

fof(f2128,plain,
    ( spl55_21
    | spl55_22 ),
    inference(avatar_split_clause,[],[f2008,f2126,f2122])).

fof(f2126,plain,
    ( spl55_22
  <=> ! [X6] : ~ v3_ordinal1(k1_zfmisc_1(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_22])])).

fof(f2008,plain,(
    ! [X6] :
      ( ~ v3_ordinal1(k1_zfmisc_1(X6))
      | v3_ordinal1(k1_xboole_0) ) ),
    inference(resolution,[],[f1593,f1597])).

fof(f2050,plain,
    ( spl55_19
    | ~ spl55_20
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f2012,f1909,f2047,f2043])).

fof(f2047,plain,
    ( spl55_20
  <=> v3_ordinal1(k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_20])])).

fof(f2012,plain,
    ( ~ v3_ordinal1(k3_zfmisc_1(sK0,sK1,sK2))
    | v3_ordinal1(sK3)
    | ~ spl55_4 ),
    inference(resolution,[],[f1593,f1911])).

fof(f2027,plain,
    ( ~ spl55_17
    | spl55_18
    | ~ spl55_4 ),
    inference(avatar_split_clause,[],[f2002,f1909,f2024,f2020])).

fof(f2002,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl55_4 ),
    inference(resolution,[],[f1583,f1911])).

fof(f1975,plain,
    ( spl55_16
    | ~ spl55_12 ),
    inference(avatar_split_clause,[],[f1957,f1949,f1972])).

fof(f1972,plain,
    ( spl55_16
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_16])])).

fof(f1957,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl55_12 ),
    inference(superposition,[],[f1597,f1951])).

fof(f1970,plain,
    ( spl55_13
    | spl55_14
    | spl55_15 ),
    inference(avatar_split_clause,[],[f1515,f1967,f1963,f1959])).

fof(f1515,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f1354])).

fof(f1354,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1347])).

fof(f1347,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1346])).

fof(f1346,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f1952,plain,(
    spl55_12 ),
    inference(avatar_split_clause,[],[f1692,f1949])).

fof(f1692,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f1947,plain,(
    spl55_11 ),
    inference(avatar_split_clause,[],[f1840,f1944])).

fof(f1944,plain,
    ( spl55_11
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_11])])).

fof(f1840,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f873])).

fof(f873,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f1942,plain,(
    spl55_10 ),
    inference(avatar_split_clause,[],[f1839,f1939])).

fof(f1939,plain,
    ( spl55_10
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_10])])).

fof(f1839,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f387])).

fof(f387,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f1937,plain,(
    spl55_9 ),
    inference(avatar_split_clause,[],[f1838,f1934])).

fof(f1934,plain,
    ( spl55_9
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_9])])).

fof(f1838,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f858])).

fof(f858,axiom,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

fof(f1932,plain,(
    spl55_8 ),
    inference(avatar_split_clause,[],[f1837,f1929])).

fof(f1929,plain,
    ( spl55_8
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_8])])).

fof(f1837,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1927,plain,(
    spl55_7 ),
    inference(avatar_split_clause,[],[f1836,f1924])).

fof(f1924,plain,
    ( spl55_7
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_7])])).

fof(f1836,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f1922,plain,(
    spl55_6 ),
    inference(avatar_split_clause,[],[f1889,f1919])).

fof(f1919,plain,
    ( spl55_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl55_6])])).

fof(f1889,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1825])).

fof(f1825,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1514])).

fof(f1514,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f1917,plain,(
    spl55_5 ),
    inference(avatar_split_clause,[],[f1841,f1914])).

fof(f1841,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1912,plain,(
    spl55_4 ),
    inference(avatar_split_clause,[],[f1516,f1909])).

fof(f1516,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1354])).

fof(f1907,plain,(
    ~ spl55_3 ),
    inference(avatar_split_clause,[],[f1519,f1904])).

fof(f1519,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1354])).

fof(f1902,plain,(
    ~ spl55_2 ),
    inference(avatar_split_clause,[],[f1518,f1899])).

fof(f1518,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1354])).

fof(f1897,plain,(
    ~ spl55_1 ),
    inference(avatar_split_clause,[],[f1517,f1894])).

fof(f1517,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1354])).
%------------------------------------------------------------------------------
