%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:28 EST 2020

% Result     : Theorem 48.82s
% Output     : Refutation 48.82s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 358 expanded)
%              Number of leaves         :   56 ( 147 expanded)
%              Depth                    :   10
%              Number of atoms          :  715 (1150 expanded)
%              Number of equality atoms :  160 ( 300 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57484,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f417,f478,f521,f526,f597,f614,f752,f791,f900,f1559,f1568,f1668,f2135,f7616,f8240,f8368,f8407,f19243,f22962,f23272,f23481,f37851,f45637,f47813,f52932,f54604,f56508,f57377,f57419,f57455,f57482])).

fof(f57482,plain,
    ( spl16_8
    | spl16_12
    | ~ spl16_574
    | ~ spl16_1139 ),
    inference(avatar_contradiction_clause,[],[f57481])).

fof(f57481,plain,
    ( $false
    | spl16_8
    | spl16_12
    | ~ spl16_574
    | ~ spl16_1139 ),
    inference(subsumption_resolution,[],[f57480,f596])).

fof(f596,plain,
    ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)
    | spl16_8 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl16_8
  <=> k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f57480,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | spl16_12
    | ~ spl16_574
    | ~ spl16_1139 ),
    inference(subsumption_resolution,[],[f57461,f613])).

fof(f613,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | spl16_12 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl16_12
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f57461,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | ~ spl16_574
    | ~ spl16_1139 ),
    inference(resolution,[],[f57454,f23271])).

fof(f23271,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tarski(X1))
        | k1_xboole_0 = X0
        | k1_tarski(X1) = X0 )
    | ~ spl16_574 ),
    inference(avatar_component_clause,[],[f23270])).

fof(f23270,plain,
    ( spl16_574
  <=> ! [X1,X0] :
        ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_574])])).

fof(f57454,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0))
    | ~ spl16_1139 ),
    inference(avatar_component_clause,[],[f57452])).

fof(f57452,plain,
    ( spl16_1139
  <=> r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1139])])).

fof(f57455,plain,
    ( spl16_1139
    | ~ spl16_5
    | ~ spl16_577
    | ~ spl16_1049
    | ~ spl16_1136 ),
    inference(avatar_split_clause,[],[f57442,f57416,f54602,f23479,f523,f57452])).

fof(f523,plain,
    ( spl16_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f23479,plain,
    ( spl16_577
  <=> ! [X7] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_577])])).

fof(f54602,plain,
    ( spl16_1049
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_setfam_1(X0,X1),X2)
        | ~ r1_tarski(X1,k7_setfam_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1049])])).

fof(f57416,plain,
    ( spl16_1136
  <=> r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1136])])).

fof(f57442,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0))
    | ~ spl16_5
    | ~ spl16_577
    | ~ spl16_1049
    | ~ spl16_1136 ),
    inference(subsumption_resolution,[],[f57441,f525])).

fof(f525,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f523])).

fof(f57441,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl16_577
    | ~ spl16_1049
    | ~ spl16_1136 ),
    inference(subsumption_resolution,[],[f57423,f23480])).

fof(f23480,plain,
    ( ! [X7] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7)))
    | ~ spl16_577 ),
    inference(avatar_component_clause,[],[f23479])).

fof(f57423,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl16_1049
    | ~ spl16_1136 ),
    inference(resolution,[],[f57418,f54603])).

fof(f54603,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
        | r1_tarski(k7_setfam_1(X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl16_1049 ),
    inference(avatar_component_clause,[],[f54602])).

fof(f57418,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl16_1136 ),
    inference(avatar_component_clause,[],[f57416])).

fof(f57419,plain,
    ( spl16_1136
    | ~ spl16_21
    | ~ spl16_1135 ),
    inference(avatar_split_clause,[],[f57408,f57375,f898,f57416])).

fof(f898,plain,
    ( spl16_21
  <=> ! [X19] :
        ( r1_tarski(sK1,X19)
        | ~ r2_hidden(sK0,X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_21])])).

fof(f57375,plain,
    ( spl16_1135
  <=> ! [X36] : r2_hidden(X36,k7_setfam_1(X36,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1135])])).

fof(f57408,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl16_21
    | ~ spl16_1135 ),
    inference(resolution,[],[f57376,f899])).

fof(f899,plain,
    ( ! [X19] :
        ( ~ r2_hidden(sK0,X19)
        | r1_tarski(sK1,X19) )
    | ~ spl16_21 ),
    inference(avatar_component_clause,[],[f898])).

fof(f57376,plain,
    ( ! [X36] : r2_hidden(X36,k7_setfam_1(X36,k1_tarski(k1_xboole_0)))
    | ~ spl16_1135 ),
    inference(avatar_component_clause,[],[f57375])).

fof(f57377,plain,
    ( spl16_1135
    | ~ spl16_494
    | ~ spl16_577
    | ~ spl16_599
    | ~ spl16_823
    | ~ spl16_1007
    | ~ spl16_1121 ),
    inference(avatar_split_clause,[],[f57368,f56506,f52930,f45635,f37849,f23479,f19241,f57375])).

fof(f19241,plain,
    ( spl16_494
  <=> ! [X3,X0] :
        ( X0 = X3
        | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_494])])).

fof(f37849,plain,
    ( spl16_599
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_599])])).

fof(f45635,plain,
    ( spl16_823
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_823])])).

fof(f52930,plain,
    ( spl16_1007
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1007])])).

fof(f56506,plain,
    ( spl16_1121
  <=> ! [X10] : r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1121])])).

fof(f57368,plain,
    ( ! [X36] : r2_hidden(X36,k7_setfam_1(X36,k1_tarski(k1_xboole_0)))
    | ~ spl16_494
    | ~ spl16_577
    | ~ spl16_599
    | ~ spl16_823
    | ~ spl16_1007
    | ~ spl16_1121 ),
    inference(forward_demodulation,[],[f57367,f46617])).

fof(f46617,plain,
    ( ! [X9] : k3_subset_1(X9,k1_xboole_0) = X9
    | ~ spl16_599
    | ~ spl16_823 ),
    inference(forward_demodulation,[],[f46586,f237])).

fof(f237,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f46586,plain,
    ( ! [X9] : k4_xboole_0(X9,k1_xboole_0) = k3_subset_1(X9,k1_xboole_0)
    | ~ spl16_599
    | ~ spl16_823 ),
    inference(resolution,[],[f45636,f37850])).

fof(f37850,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl16_599 ),
    inference(avatar_component_clause,[],[f37849])).

fof(f45636,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl16_823 ),
    inference(avatar_component_clause,[],[f45635])).

fof(f57367,plain,
    ( ! [X36] : r2_hidden(k3_subset_1(X36,k1_xboole_0),k7_setfam_1(X36,k1_tarski(k1_xboole_0)))
    | ~ spl16_494
    | ~ spl16_577
    | ~ spl16_1007
    | ~ spl16_1121 ),
    inference(forward_demodulation,[],[f57366,f57244])).

fof(f57244,plain,
    ( ! [X7] : k1_xboole_0 = sK5(k1_zfmisc_1(X7),k1_tarski(k1_xboole_0))
    | ~ spl16_494
    | ~ spl16_1121 ),
    inference(resolution,[],[f56507,f19242])).

fof(f19242,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_tarski(X0))
        | X0 = X3 )
    | ~ spl16_494 ),
    inference(avatar_component_clause,[],[f19241])).

fof(f56507,plain,
    ( ! [X10] : r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | ~ spl16_1121 ),
    inference(avatar_component_clause,[],[f56506])).

fof(f57366,plain,
    ( ! [X37,X36] : r2_hidden(k3_subset_1(X36,sK5(k1_zfmisc_1(X37),k1_tarski(k1_xboole_0))),k7_setfam_1(X36,k1_tarski(k1_xboole_0)))
    | ~ spl16_577
    | ~ spl16_1007
    | ~ spl16_1121 ),
    inference(subsumption_resolution,[],[f57268,f23480])).

fof(f57268,plain,
    ( ! [X37,X36] :
        ( r2_hidden(k3_subset_1(X36,sK5(k1_zfmisc_1(X37),k1_tarski(k1_xboole_0))),k7_setfam_1(X36,k1_tarski(k1_xboole_0)))
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X36))) )
    | ~ spl16_1007
    | ~ spl16_1121 ),
    inference(resolution,[],[f56507,f52931])).

fof(f52931,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl16_1007 ),
    inference(avatar_component_clause,[],[f52930])).

fof(f56508,plain,
    ( spl16_1121
    | ~ spl16_63
    | ~ spl16_577
    | ~ spl16_873 ),
    inference(avatar_split_clause,[],[f48960,f47811,f23479,f2133,f56506])).

fof(f2133,plain,
    ( spl16_63
  <=> ! [X3] : k1_xboole_0 != k1_tarski(X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_63])])).

fof(f47811,plain,
    ( spl16_873
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_873])])).

fof(f48960,plain,
    ( ! [X10] : r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | ~ spl16_63
    | ~ spl16_577
    | ~ spl16_873 ),
    inference(subsumption_resolution,[],[f48935,f2134])).

fof(f2134,plain,
    ( ! [X3] : k1_xboole_0 != k1_tarski(X3)
    | ~ spl16_63 ),
    inference(avatar_component_clause,[],[f2133])).

fof(f48935,plain,
    ( ! [X10] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) )
    | ~ spl16_577
    | ~ spl16_873 ),
    inference(resolution,[],[f47812,f23480])).

fof(f47812,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1
        | r2_hidden(sK5(X0,X1),X1) )
    | ~ spl16_873 ),
    inference(avatar_component_clause,[],[f47811])).

fof(f54604,plain,(
    spl16_1049 ),
    inference(avatar_split_clause,[],[f290,f54602])).

fof(f290,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
              | ~ r1_tarski(X1,k7_setfam_1(X0,X2)) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f52932,plain,(
    spl16_1007 ),
    inference(avatar_split_clause,[],[f37355,f52930])).

fof(f37355,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f281,f350])).

fof(f350,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f154])).

fof(f154,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f95])).

fof(f95,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f94])).

fof(f94,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f47813,plain,(
    spl16_873 ),
    inference(avatar_split_clause,[],[f275,f47811])).

fof(f275,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f122,f170])).

fof(f170,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f84])).

fof(f84,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f45637,plain,(
    spl16_823 ),
    inference(avatar_split_clause,[],[f272,f45635])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f37851,plain,(
    spl16_599 ),
    inference(avatar_split_clause,[],[f235,f37849])).

fof(f235,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f23481,plain,
    ( spl16_577
    | ~ spl16_270
    | ~ spl16_570 ),
    inference(avatar_split_clause,[],[f23430,f22960,f8405,f23479])).

fof(f8405,plain,
    ( spl16_270
  <=> ! [X0] : k1_xboole_0 != k1_zfmisc_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_270])])).

fof(f22960,plain,
    ( spl16_570
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_570])])).

fof(f23430,plain,
    ( ! [X7] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7)))
    | ~ spl16_270
    | ~ spl16_570 ),
    inference(subsumption_resolution,[],[f23387,f8406])).

fof(f8406,plain,
    ( ! [X0] : k1_xboole_0 != k1_zfmisc_1(X0)
    | ~ spl16_270 ),
    inference(avatar_component_clause,[],[f8405])).

fof(f23387,plain,
    ( ! [X7] :
        ( k1_xboole_0 = k1_zfmisc_1(X7)
        | m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7))) )
    | ~ spl16_570 ),
    inference(resolution,[],[f22961,f235])).

fof(f22961,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k1_xboole_0 = X0
        | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) )
    | ~ spl16_570 ),
    inference(avatar_component_clause,[],[f22960])).

fof(f23272,plain,(
    spl16_574 ),
    inference(avatar_split_clause,[],[f314,f23270])).

fof(f314,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f22962,plain,(
    spl16_570 ),
    inference(avatar_split_clause,[],[f264,f22960])).

fof(f264,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f19243,plain,(
    spl16_494 ),
    inference(avatar_split_clause,[],[f391,f19241])).

fof(f391,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f304])).

fof(f304,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK8(X0,X1) != X0
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sK8(X0,X1) = X0
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f187,f188])).

fof(f188,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK8(X0,X1) != X0
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sK8(X0,X1) = X0
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f187,plain,(
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
    inference(rectify,[],[f186])).

fof(f186,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f8407,plain,
    ( spl16_270
    | ~ spl16_268 ),
    inference(avatar_split_clause,[],[f8392,f8366,f8405])).

fof(f8366,plain,
    ( spl16_268
  <=> ! [X5] : k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(X5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_268])])).

fof(f8392,plain,
    ( ! [X0] : k1_xboole_0 != k1_zfmisc_1(X0)
    | ~ spl16_268 ),
    inference(superposition,[],[f8367,f237])).

fof(f8367,plain,
    ( ! [X5] : k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(X5),k1_xboole_0)
    | ~ spl16_268 ),
    inference(avatar_component_clause,[],[f8366])).

fof(f8368,plain,
    ( spl16_268
    | ~ spl16_266 ),
    inference(avatar_split_clause,[],[f8245,f8238,f8366])).

fof(f8238,plain,
    ( spl16_266
  <=> ! [X7] : ~ r1_tarski(k1_zfmisc_1(X7),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_266])])).

fof(f8245,plain,
    ( ! [X5] : k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(X5),k1_xboole_0)
    | ~ spl16_266 ),
    inference(resolution,[],[f8239,f319])).

fof(f319,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f8239,plain,
    ( ! [X7] : ~ r1_tarski(k1_zfmisc_1(X7),k1_xboole_0)
    | ~ spl16_266 ),
    inference(avatar_component_clause,[],[f8238])).

fof(f8240,plain,
    ( spl16_266
    | ~ spl16_240 ),
    inference(avatar_split_clause,[],[f8210,f7614,f8238])).

fof(f7614,plain,
    ( spl16_240
  <=> ! [X9,X10] :
        ( ~ r1_tarski(X10,k1_xboole_0)
        | ~ r1_tarski(k1_tarski(X9),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_240])])).

fof(f8210,plain,
    ( ! [X7] : ~ r1_tarski(k1_zfmisc_1(X7),k1_xboole_0)
    | ~ spl16_240 ),
    inference(resolution,[],[f7615,f239])).

fof(f239,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f7615,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(k1_tarski(X9),X10)
        | ~ r1_tarski(X10,k1_xboole_0) )
    | ~ spl16_240 ),
    inference(avatar_component_clause,[],[f7614])).

fof(f7616,plain,
    ( spl16_240
    | ~ spl16_52 ),
    inference(avatar_split_clause,[],[f1681,f1666,f7614])).

fof(f1666,plain,
    ( spl16_52
  <=> ! [X60] : ~ r1_tarski(k1_tarski(X60),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).

fof(f1681,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(X10,k1_xboole_0)
        | ~ r1_tarski(k1_tarski(X9),X10) )
    | ~ spl16_52 ),
    inference(resolution,[],[f1667,f351])).

fof(f351,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f157])).

fof(f157,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f156])).

fof(f156,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1667,plain,
    ( ! [X60] : ~ r1_tarski(k1_tarski(X60),k1_xboole_0)
    | ~ spl16_52 ),
    inference(avatar_component_clause,[],[f1666])).

fof(f2135,plain,
    ( spl16_63
    | ~ spl16_47 ),
    inference(avatar_split_clause,[],[f2131,f1566,f2133])).

fof(f1566,plain,
    ( spl16_47
  <=> ! [X9] : k1_xboole_0 != k4_xboole_0(k1_tarski(X9),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_47])])).

fof(f2131,plain,
    ( ! [X3] : k1_xboole_0 != k1_tarski(X3)
    | ~ spl16_47 ),
    inference(subsumption_resolution,[],[f2124,f1567])).

fof(f1567,plain,
    ( ! [X9] : k1_xboole_0 != k4_xboole_0(k1_tarski(X9),k1_xboole_0)
    | ~ spl16_47 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f2124,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k1_tarski(X3)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_xboole_0) )
    | ~ spl16_47 ),
    inference(superposition,[],[f1567,f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f1668,plain,
    ( spl16_52
    | ~ spl16_45 ),
    inference(avatar_split_clause,[],[f1599,f1557,f1666])).

fof(f1557,plain,
    ( spl16_45
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X6,X7)
        | ~ r1_tarski(X7,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f1599,plain,
    ( ! [X60] : ~ r1_tarski(k1_tarski(X60),k1_xboole_0)
    | ~ spl16_45 ),
    inference(resolution,[],[f1558,f390])).

fof(f390,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f389])).

fof(f389,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f305])).

fof(f305,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f189])).

fof(f1558,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,X7)
        | ~ r1_tarski(X7,k1_xboole_0) )
    | ~ spl16_45 ),
    inference(avatar_component_clause,[],[f1557])).

fof(f1568,plain,
    ( spl16_47
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f798,f789,f1566])).

fof(f789,plain,
    ( spl16_16
  <=> ! [X12] : ~ r2_hidden(X12,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).

fof(f798,plain,
    ( ! [X9] : k1_xboole_0 != k4_xboole_0(k1_tarski(X9),k1_xboole_0)
    | ~ spl16_16 ),
    inference(resolution,[],[f790,f321])).

fof(f321,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f790,plain,
    ( ! [X12] : ~ r2_hidden(X12,k1_xboole_0)
    | ~ spl16_16 ),
    inference(avatar_component_clause,[],[f789])).

fof(f1559,plain,
    ( spl16_45
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f796,f789,f1557])).

fof(f796,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,X7)
        | ~ r1_tarski(X7,k1_xboole_0) )
    | ~ spl16_16 ),
    inference(resolution,[],[f790,f301])).

fof(f301,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f183,f184])).

fof(f184,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f900,plain,
    ( spl16_21
    | ~ spl16_1 ),
    inference(avatar_split_clause,[],[f448,f414,f898])).

fof(f414,plain,
    ( spl16_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f448,plain,
    ( ! [X19] :
        ( r1_tarski(sK1,X19)
        | ~ r2_hidden(sK0,X19) )
    | ~ spl16_1 ),
    inference(superposition,[],[f318,f416])).

fof(f416,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl16_1 ),
    inference(avatar_component_clause,[],[f414])).

fof(f318,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f791,plain,
    ( spl16_16
    | ~ spl16_14 ),
    inference(avatar_split_clause,[],[f787,f749,f789])).

fof(f749,plain,
    ( spl16_14
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).

fof(f787,plain,
    ( ! [X12] : ~ r2_hidden(X12,k1_xboole_0)
    | ~ spl16_14 ),
    inference(subsumption_resolution,[],[f781,f780])).

fof(f780,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,k1_xboole_0)
        | ~ r2_hidden(X11,sK1) )
    | ~ spl16_14 ),
    inference(superposition,[],[f403,f751])).

fof(f751,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl16_14 ),
    inference(avatar_component_clause,[],[f749])).

fof(f403,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f360])).

fof(f360,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f217])).

fof(f217,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK14(X0,X1,X2),X1)
            | ~ r2_hidden(sK14(X0,X1,X2),X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),X0) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f215,f216])).

fof(f216,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK14(X0,X1,X2),X1)
          | ~ r2_hidden(sK14(X0,X1,X2),X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            & r2_hidden(sK14(X0,X1,X2),X0) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f215,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f214])).

fof(f214,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f213])).

fof(f213,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f781,plain,
    ( ! [X12] :
        ( ~ r2_hidden(X12,k1_xboole_0)
        | r2_hidden(X12,sK1) )
    | ~ spl16_14 ),
    inference(superposition,[],[f404,f751])).

fof(f404,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f359])).

fof(f359,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f217])).

fof(f752,plain,
    ( spl16_14
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f508,f475,f414,f749])).

fof(f475,plain,
    ( spl16_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f508,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(forward_demodulation,[],[f493,f416])).

fof(f493,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl16_2 ),
    inference(resolution,[],[f477,f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f199])).

fof(f477,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f475])).

fof(f614,plain,
    ( ~ spl16_12
    | spl16_4
    | ~ spl16_5 ),
    inference(avatar_split_clause,[],[f587,f523,f518,f611])).

fof(f518,plain,
    ( spl16_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f587,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f551,f520])).

fof(f520,plain,
    ( k1_xboole_0 != sK1
    | spl16_4 ),
    inference(avatar_component_clause,[],[f518])).

fof(f551,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl16_5 ),
    inference(resolution,[],[f525,f279])).

fof(f279,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f93])).

fof(f93,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f597,plain,(
    ~ spl16_8 ),
    inference(avatar_split_clause,[],[f231,f594])).

fof(f231,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f163])).

fof(f163,plain,
    ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)
    & sK1 = k1_tarski(sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f104,f162])).

fof(f162,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
        & k1_tarski(X0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)
      & sK1 = k1_tarski(sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f100])).

fof(f100,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f99])).

fof(f99,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f526,plain,(
    spl16_5 ),
    inference(avatar_split_clause,[],[f229,f523])).

fof(f229,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f163])).

fof(f521,plain,
    ( ~ spl16_4
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f510,f475,f414,f518])).

fof(f510,plain,
    ( k1_xboole_0 != sK1
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(forward_demodulation,[],[f509,f508])).

fof(f509,plain,
    ( sK1 != k4_xboole_0(sK1,sK1)
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(forward_demodulation,[],[f494,f416])).

fof(f494,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl16_2 ),
    inference(resolution,[],[f477,f323])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f478,plain,
    ( spl16_2
    | ~ spl16_1 ),
    inference(avatar_split_clause,[],[f466,f414,f475])).

fof(f466,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl16_1 ),
    inference(superposition,[],[f390,f416])).

fof(f417,plain,(
    spl16_1 ),
    inference(avatar_split_clause,[],[f230,f414])).

fof(f230,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (12349)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (12343)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (12348)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12341)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (12344)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (12352)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (12342)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (12371)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (12362)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (12360)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (12350)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (12338)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (12339)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12340)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (12369)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (12354)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (12370)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12346)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (12368)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (12363)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (12345)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (12367)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (12355)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (12366)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.56  % (12351)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.56  % (12353)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.56  % (12358)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.56  % (12357)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.56  % (12359)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.57  % (12365)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 3.18/0.84  % (12343)Time limit reached!
% 3.18/0.84  % (12343)------------------------------
% 3.18/0.84  % (12343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.18/0.84  % (12343)Termination reason: Time limit
% 3.18/0.84  % (12343)Termination phase: Saturation
% 3.18/0.84  
% 3.18/0.84  % (12343)Memory used [KB]: 9594
% 3.18/0.84  % (12343)Time elapsed: 0.400 s
% 3.18/0.84  % (12343)------------------------------
% 3.18/0.84  % (12343)------------------------------
% 4.00/0.91  % (12357)Time limit reached!
% 4.00/0.91  % (12357)------------------------------
% 4.00/0.91  % (12357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.91  % (12357)Termination reason: Time limit
% 4.00/0.91  
% 4.00/0.91  % (12357)Memory used [KB]: 14072
% 4.00/0.91  % (12357)Time elapsed: 0.508 s
% 4.00/0.91  % (12357)------------------------------
% 4.00/0.91  % (12357)------------------------------
% 4.00/0.92  % (12338)Time limit reached!
% 4.00/0.92  % (12338)------------------------------
% 4.00/0.92  % (12338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.92  % (12338)Termination reason: Time limit
% 4.00/0.92  % (12338)Termination phase: Saturation
% 4.00/0.92  
% 4.00/0.92  % (12338)Memory used [KB]: 4093
% 4.00/0.92  % (12338)Time elapsed: 0.500 s
% 4.00/0.92  % (12338)------------------------------
% 4.00/0.92  % (12338)------------------------------
% 4.00/0.92  % (12339)Time limit reached!
% 4.00/0.92  % (12339)------------------------------
% 4.00/0.92  % (12339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.92  % (12339)Termination reason: Time limit
% 4.00/0.92  % (12339)Termination phase: Saturation
% 4.00/0.92  
% 4.00/0.92  % (12339)Memory used [KB]: 8571
% 4.00/0.92  % (12339)Time elapsed: 0.500 s
% 4.00/0.92  % (12339)------------------------------
% 4.00/0.92  % (12339)------------------------------
% 4.38/0.93  % (12349)Time limit reached!
% 4.38/0.93  % (12349)------------------------------
% 4.38/0.93  % (12349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.93  % (12349)Termination reason: Time limit
% 4.38/0.93  
% 4.38/0.93  % (12349)Memory used [KB]: 14711
% 4.38/0.93  % (12349)Time elapsed: 0.515 s
% 4.38/0.93  % (12349)------------------------------
% 4.38/0.93  % (12349)------------------------------
% 4.38/0.94  % (12351)Time limit reached!
% 4.38/0.94  % (12351)------------------------------
% 4.38/0.94  % (12351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.94  % (12351)Termination reason: Time limit
% 4.38/0.94  % (12351)Termination phase: Saturation
% 4.38/0.94  
% 4.38/0.94  % (12351)Memory used [KB]: 8443
% 4.38/0.94  % (12351)Time elapsed: 0.500 s
% 4.38/0.94  % (12351)------------------------------
% 4.38/0.94  % (12351)------------------------------
% 4.62/0.98  % (12461)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.62/1.01  % (12355)Time limit reached!
% 4.62/1.01  % (12355)------------------------------
% 4.62/1.01  % (12355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/1.01  % (12355)Termination reason: Time limit
% 4.62/1.01  % (12355)Termination phase: Saturation
% 4.62/1.01  
% 4.62/1.01  % (12355)Memory used [KB]: 17782
% 4.62/1.01  % (12355)Time elapsed: 0.600 s
% 4.62/1.01  % (12355)------------------------------
% 4.62/1.01  % (12355)------------------------------
% 4.62/1.02  % (12499)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.05/1.03  % (12370)Time limit reached!
% 5.05/1.03  % (12370)------------------------------
% 5.05/1.03  % (12370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.05/1.04  % (12503)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.05/1.05  % (12370)Termination reason: Time limit
% 5.05/1.05  
% 5.05/1.05  % (12370)Memory used [KB]: 10746
% 5.05/1.05  % (12370)Time elapsed: 0.605 s
% 5.05/1.05  % (12370)------------------------------
% 5.05/1.05  % (12370)------------------------------
% 5.05/1.06  % (12511)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.05/1.06  % (12345)Time limit reached!
% 5.05/1.06  % (12345)------------------------------
% 5.05/1.06  % (12345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.05/1.06  % (12345)Termination reason: Time limit
% 5.05/1.06  % (12345)Termination phase: Saturation
% 5.05/1.06  
% 5.05/1.06  % (12345)Memory used [KB]: 10874
% 5.05/1.06  % (12345)Time elapsed: 0.600 s
% 5.05/1.06  % (12345)------------------------------
% 5.05/1.06  % (12345)------------------------------
% 5.05/1.08  % (12513)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.60/1.09  % (12508)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.60/1.10  % (12549)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.60/1.15  % (12587)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.43/1.21  % (12588)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.91/1.25  % (12362)Time limit reached!
% 6.91/1.25  % (12362)------------------------------
% 6.91/1.25  % (12362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.91/1.25  % (12362)Termination reason: Time limit
% 6.91/1.25  % (12362)Termination phase: Saturation
% 6.91/1.25  
% 6.91/1.25  % (12362)Memory used [KB]: 6012
% 6.91/1.25  % (12362)Time elapsed: 0.800 s
% 6.91/1.25  % (12362)------------------------------
% 6.91/1.25  % (12362)------------------------------
% 7.88/1.39  % (12649)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.88/1.39  % (12511)Time limit reached!
% 7.88/1.39  % (12511)------------------------------
% 7.88/1.39  % (12511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.39  % (12511)Termination reason: Time limit
% 7.88/1.39  
% 7.88/1.39  % (12511)Memory used [KB]: 13560
% 7.88/1.39  % (12511)Time elapsed: 0.420 s
% 7.88/1.39  % (12511)------------------------------
% 7.88/1.39  % (12511)------------------------------
% 7.88/1.39  % (12508)Time limit reached!
% 7.88/1.39  % (12508)------------------------------
% 7.88/1.39  % (12508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.39  % (12508)Termination reason: Time limit
% 7.88/1.39  
% 7.88/1.39  % (12508)Memory used [KB]: 7803
% 7.88/1.39  % (12508)Time elapsed: 0.423 s
% 7.88/1.39  % (12508)------------------------------
% 7.88/1.39  % (12508)------------------------------
% 7.88/1.42  % (12340)Time limit reached!
% 7.88/1.42  % (12340)------------------------------
% 7.88/1.42  % (12340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.42  % (12340)Termination reason: Time limit
% 7.88/1.42  
% 7.88/1.42  % (12340)Memory used [KB]: 22387
% 7.88/1.42  % (12340)Time elapsed: 1.004 s
% 7.88/1.42  % (12340)------------------------------
% 7.88/1.42  % (12340)------------------------------
% 8.74/1.52  % (12699)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.04/1.53  % (12698)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 9.14/1.57  % (12700)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.91/1.62  % (12363)Time limit reached!
% 9.91/1.62  % (12363)------------------------------
% 9.91/1.62  % (12363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.91/1.62  % (12363)Termination reason: Time limit
% 9.91/1.62  
% 9.91/1.62  % (12363)Memory used [KB]: 18677
% 9.91/1.62  % (12363)Time elapsed: 1.207 s
% 9.91/1.62  % (12363)------------------------------
% 9.91/1.62  % (12363)------------------------------
% 9.91/1.64  % (12368)Time limit reached!
% 9.91/1.64  % (12368)------------------------------
% 9.91/1.64  % (12368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.91/1.64  % (12368)Termination reason: Time limit
% 9.91/1.64  
% 9.91/1.64  % (12368)Memory used [KB]: 18421
% 9.91/1.64  % (12368)Time elapsed: 1.228 s
% 9.91/1.64  % (12368)------------------------------
% 9.91/1.64  % (12368)------------------------------
% 10.38/1.74  % (12366)Time limit reached!
% 10.38/1.74  % (12366)------------------------------
% 10.38/1.74  % (12366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.38/1.74  % (12366)Termination reason: Time limit
% 10.38/1.74  
% 10.38/1.74  % (12366)Memory used [KB]: 24306
% 10.38/1.74  % (12366)Time elapsed: 1.314 s
% 10.38/1.74  % (12366)------------------------------
% 10.38/1.74  % (12366)------------------------------
% 10.38/1.75  % (12701)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 10.38/1.76  % (12354)Time limit reached!
% 10.38/1.76  % (12354)------------------------------
% 10.38/1.76  % (12354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.02/1.76  % (12702)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.02/1.78  % (12354)Termination reason: Time limit
% 11.02/1.78  % (12354)Termination phase: Saturation
% 11.02/1.78  
% 11.02/1.78  % (12354)Memory used [KB]: 17270
% 11.02/1.78  % (12354)Time elapsed: 1.300 s
% 11.02/1.78  % (12354)------------------------------
% 11.02/1.78  % (12354)------------------------------
% 11.46/1.88  % (12703)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 12.07/1.92  % (12704)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.07/1.93  % (12342)Time limit reached!
% 12.07/1.93  % (12342)------------------------------
% 12.07/1.93  % (12342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.07/1.95  % (12369)Time limit reached!
% 12.07/1.95  % (12369)------------------------------
% 12.07/1.95  % (12369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.07/1.95  % (12369)Termination reason: Time limit
% 12.07/1.95  
% 12.07/1.95  % (12369)Memory used [KB]: 14839
% 12.07/1.95  % (12369)Time elapsed: 1.538 s
% 12.07/1.95  % (12369)------------------------------
% 12.07/1.95  % (12369)------------------------------
% 12.07/1.95  % (12342)Termination reason: Time limit
% 12.07/1.95  
% 12.07/1.95  % (12342)Memory used [KB]: 16630
% 12.07/1.95  % (12342)Time elapsed: 1.519 s
% 12.07/1.95  % (12342)------------------------------
% 12.07/1.95  % (12342)------------------------------
% 12.53/1.98  % (12700)Time limit reached!
% 12.53/1.98  % (12700)------------------------------
% 12.53/1.98  % (12700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.99  % (12700)Termination reason: Time limit
% 12.53/1.99  % (12700)Termination phase: Saturation
% 12.53/1.99  
% 12.53/1.99  % (12700)Memory used [KB]: 3454
% 12.53/1.99  % (12700)Time elapsed: 0.500 s
% 12.53/1.99  % (12700)------------------------------
% 12.53/1.99  % (12700)------------------------------
% 12.53/2.01  % (12350)Time limit reached!
% 12.53/2.01  % (12350)------------------------------
% 12.53/2.01  % (12350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/2.01  % (12350)Termination reason: Time limit
% 12.53/2.01  % (12350)Termination phase: Saturation
% 12.53/2.01  
% 12.53/2.01  % (12350)Memory used [KB]: 19061
% 12.53/2.01  % (12350)Time elapsed: 1.600 s
% 12.53/2.01  % (12350)------------------------------
% 12.53/2.01  % (12350)------------------------------
% 13.07/2.06  % (12706)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.07/2.08  % (12705)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.16/2.11  % (12707)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.37/2.11  % (12708)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.08/2.22  % (12704)Time limit reached!
% 14.08/2.22  % (12704)------------------------------
% 14.08/2.22  % (12704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.08/2.22  % (12704)Termination reason: Time limit
% 14.08/2.22  
% 14.08/2.22  % (12704)Memory used [KB]: 4733
% 14.08/2.22  % (12704)Time elapsed: 0.405 s
% 14.08/2.22  % (12704)------------------------------
% 14.08/2.22  % (12704)------------------------------
% 14.75/2.23  % (12353)Time limit reached!
% 14.75/2.23  % (12353)------------------------------
% 14.75/2.23  % (12353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.24  % (12549)Time limit reached!
% 14.75/2.24  % (12549)------------------------------
% 14.75/2.24  % (12549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.24  % (12353)Termination reason: Time limit
% 14.75/2.24  
% 14.75/2.24  % (12353)Memory used [KB]: 8955
% 14.75/2.24  % (12353)Time elapsed: 1.807 s
% 14.75/2.24  % (12353)------------------------------
% 14.75/2.24  % (12353)------------------------------
% 14.75/2.25  % (12549)Termination reason: Time limit
% 14.75/2.25  
% 14.75/2.25  % (12549)Memory used [KB]: 11257
% 14.75/2.25  % (12549)Time elapsed: 1.207 s
% 14.75/2.25  % (12549)------------------------------
% 14.75/2.25  % (12549)------------------------------
% 15.24/2.34  % (12709)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.85/2.38  % (12710)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.85/2.39  % (12711)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.08/2.42  % (12707)Time limit reached!
% 16.08/2.42  % (12707)------------------------------
% 16.08/2.42  % (12707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.08/2.43  % (12358)Time limit reached!
% 16.08/2.43  % (12358)------------------------------
% 16.08/2.43  % (12358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.26/2.43  % (12707)Termination reason: Time limit
% 16.26/2.43  % (12707)Termination phase: Saturation
% 16.26/2.43  
% 16.26/2.43  % (12707)Memory used [KB]: 3070
% 16.26/2.43  % (12707)Time elapsed: 0.400 s
% 16.26/2.43  % (12707)------------------------------
% 16.26/2.43  % (12707)------------------------------
% 16.26/2.44  % (12358)Termination reason: Time limit
% 16.26/2.44  
% 16.26/2.44  % (12358)Memory used [KB]: 18421
% 16.26/2.44  % (12358)Time elapsed: 2.014 s
% 16.26/2.44  % (12358)------------------------------
% 16.26/2.44  % (12358)------------------------------
% 16.26/2.45  % (12344)Time limit reached!
% 16.26/2.45  % (12344)------------------------------
% 16.26/2.45  % (12344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.26/2.45  % (12344)Termination reason: Time limit
% 16.26/2.45  % (12344)Termination phase: Saturation
% 16.26/2.45  
% 16.26/2.45  % (12344)Memory used [KB]: 27632
% 16.26/2.45  % (12344)Time elapsed: 2.0000 s
% 16.26/2.45  % (12344)------------------------------
% 16.26/2.45  % (12344)------------------------------
% 16.87/2.56  % (12713)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.87/2.57  % (12712)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.87/2.58  % (12714)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.84/2.70  % (12503)Time limit reached!
% 17.84/2.70  % (12503)------------------------------
% 17.84/2.70  % (12503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.84/2.70  % (12503)Termination reason: Time limit
% 17.84/2.70  
% 17.84/2.70  % (12503)Memory used [KB]: 17910
% 17.84/2.70  % (12503)Time elapsed: 1.707 s
% 17.84/2.70  % (12503)------------------------------
% 17.84/2.70  % (12503)------------------------------
% 18.85/2.83  % (12588)Time limit reached!
% 18.85/2.83  % (12588)------------------------------
% 18.85/2.83  % (12588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.55/2.83  % (12588)Termination reason: Time limit
% 19.55/2.83  
% 19.55/2.83  % (12588)Memory used [KB]: 15095
% 19.55/2.83  % (12588)Time elapsed: 1.718 s
% 19.55/2.83  % (12588)------------------------------
% 19.55/2.83  % (12588)------------------------------
% 19.55/2.84  % (12715)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.55/2.88  % (12712)Time limit reached!
% 19.55/2.88  % (12712)------------------------------
% 19.55/2.88  % (12712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.55/2.88  % (12712)Termination reason: Time limit
% 19.55/2.88  
% 19.55/2.88  % (12712)Memory used [KB]: 10490
% 19.55/2.88  % (12712)Time elapsed: 0.424 s
% 19.55/2.88  % (12712)------------------------------
% 19.55/2.88  % (12712)------------------------------
% 20.03/2.92  % (12714)Time limit reached!
% 20.03/2.92  % (12714)------------------------------
% 20.03/2.92  % (12714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.03/2.92  % (12714)Termination reason: Time limit
% 20.03/2.92  
% 20.03/2.92  % (12714)Memory used [KB]: 11641
% 20.03/2.92  % (12714)Time elapsed: 0.417 s
% 20.03/2.92  % (12714)------------------------------
% 20.03/2.92  % (12714)------------------------------
% 20.63/2.97  % (12703)Time limit reached!
% 20.63/2.97  % (12703)------------------------------
% 20.63/2.97  % (12703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.63/2.99  % (12703)Termination reason: Time limit
% 20.63/3.00  
% 20.63/3.00  % (12703)Memory used [KB]: 14456
% 20.63/3.00  % (12703)Time elapsed: 1.207 s
% 20.63/3.00  % (12703)------------------------------
% 20.63/3.00  % (12703)------------------------------
% 21.01/3.01  % (12359)Time limit reached!
% 21.01/3.01  % (12359)------------------------------
% 21.01/3.01  % (12359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.01/3.01  % (12359)Termination reason: Time limit
% 21.01/3.01  % (12359)Termination phase: Saturation
% 21.01/3.01  
% 21.01/3.01  % (12359)Memory used [KB]: 30319
% 21.01/3.01  % (12359)Time elapsed: 2.600 s
% 21.01/3.01  % (12359)------------------------------
% 21.01/3.01  % (12359)------------------------------
% 21.29/3.04  % (12346)Time limit reached!
% 21.29/3.04  % (12346)------------------------------
% 21.29/3.04  % (12346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.29/3.05  % (12346)Termination reason: Time limit
% 21.29/3.05  
% 21.29/3.05  % (12346)Memory used [KB]: 25585
% 21.29/3.05  % (12346)Time elapsed: 2.607 s
% 21.29/3.05  % (12346)------------------------------
% 21.29/3.05  % (12346)------------------------------
% 23.11/3.30  % (12706)Time limit reached!
% 23.11/3.30  % (12706)------------------------------
% 23.11/3.30  % (12706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.49/3.32  % (12706)Termination reason: Time limit
% 23.49/3.32  
% 23.49/3.32  % (12706)Memory used [KB]: 9083
% 23.49/3.32  % (12706)Time elapsed: 1.317 s
% 23.49/3.32  % (12706)------------------------------
% 23.49/3.32  % (12706)------------------------------
% 24.39/3.45  % (12352)Time limit reached!
% 24.39/3.45  % (12352)------------------------------
% 24.39/3.45  % (12352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.39/3.46  % (12352)Termination reason: Time limit
% 24.39/3.46  
% 24.39/3.46  % (12352)Memory used [KB]: 24690
% 24.39/3.46  % (12352)Time elapsed: 3.023 s
% 24.39/3.46  % (12352)------------------------------
% 24.39/3.46  % (12352)------------------------------
% 29.53/4.13  % (12499)Time limit reached!
% 29.53/4.13  % (12499)------------------------------
% 29.53/4.13  % (12499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.53/4.14  % (12499)Termination reason: Time limit
% 29.53/4.14  
% 29.53/4.14  % (12499)Memory used [KB]: 18293
% 29.53/4.14  % (12499)Time elapsed: 3.141 s
% 29.53/4.14  % (12499)------------------------------
% 29.53/4.14  % (12499)------------------------------
% 31.54/4.35  % (12371)Time limit reached!
% 31.54/4.35  % (12371)------------------------------
% 31.54/4.35  % (12371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.54/4.35  % (12371)Termination reason: Time limit
% 31.54/4.35  % (12371)Termination phase: Saturation
% 31.54/4.35  
% 31.54/4.35  % (12371)Memory used [KB]: 35820
% 31.54/4.35  % (12371)Time elapsed: 3.900 s
% 31.54/4.35  % (12371)------------------------------
% 31.54/4.35  % (12371)------------------------------
% 36.82/5.03  % (12348)Time limit reached!
% 36.82/5.03  % (12348)------------------------------
% 36.82/5.03  % (12348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.82/5.03  % (12348)Termination reason: Time limit
% 36.82/5.03  
% 36.82/5.03  % (12348)Memory used [KB]: 33773
% 36.82/5.03  % (12348)Time elapsed: 4.607 s
% 36.82/5.03  % (12348)------------------------------
% 36.82/5.03  % (12348)------------------------------
% 38.00/5.17  % (12702)Time limit reached!
% 38.00/5.17  % (12702)------------------------------
% 38.00/5.17  % (12702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.00/5.17  % (12702)Termination reason: Time limit
% 38.00/5.17  % (12702)Termination phase: Saturation
% 38.00/5.17  
% 38.00/5.17  % (12702)Memory used [KB]: 57696
% 38.00/5.17  % (12702)Time elapsed: 3.500 s
% 38.00/5.17  % (12702)------------------------------
% 38.00/5.17  % (12702)------------------------------
% 41.68/5.62  % (12341)Time limit reached!
% 41.68/5.62  % (12341)------------------------------
% 41.68/5.62  % (12341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.68/5.62  % (12341)Termination reason: Time limit
% 41.68/5.62  
% 41.68/5.62  % (12341)Memory used [KB]: 49636
% 41.68/5.62  % (12341)Time elapsed: 5.207 s
% 41.68/5.62  % (12341)------------------------------
% 41.68/5.62  % (12341)------------------------------
% 48.82/6.55  % (12715)Refutation found. Thanks to Tanya!
% 48.82/6.55  % SZS status Theorem for theBenchmark
% 48.82/6.55  % SZS output start Proof for theBenchmark
% 48.82/6.55  fof(f57484,plain,(
% 48.82/6.55    $false),
% 48.82/6.55    inference(avatar_sat_refutation,[],[f417,f478,f521,f526,f597,f614,f752,f791,f900,f1559,f1568,f1668,f2135,f7616,f8240,f8368,f8407,f19243,f22962,f23272,f23481,f37851,f45637,f47813,f52932,f54604,f56508,f57377,f57419,f57455,f57482])).
% 48.82/6.55  fof(f57482,plain,(
% 48.82/6.55    spl16_8 | spl16_12 | ~spl16_574 | ~spl16_1139),
% 48.82/6.55    inference(avatar_contradiction_clause,[],[f57481])).
% 48.82/6.55  fof(f57481,plain,(
% 48.82/6.55    $false | (spl16_8 | spl16_12 | ~spl16_574 | ~spl16_1139)),
% 48.82/6.55    inference(subsumption_resolution,[],[f57480,f596])).
% 48.82/6.55  fof(f596,plain,(
% 48.82/6.55    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) | spl16_8),
% 48.82/6.55    inference(avatar_component_clause,[],[f594])).
% 48.82/6.55  fof(f594,plain,(
% 48.82/6.55    spl16_8 <=> k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).
% 48.82/6.55  fof(f57480,plain,(
% 48.82/6.55    k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) | (spl16_12 | ~spl16_574 | ~spl16_1139)),
% 48.82/6.55    inference(subsumption_resolution,[],[f57461,f613])).
% 48.82/6.55  fof(f613,plain,(
% 48.82/6.55    k1_xboole_0 != k7_setfam_1(sK0,sK1) | spl16_12),
% 48.82/6.55    inference(avatar_component_clause,[],[f611])).
% 48.82/6.55  fof(f611,plain,(
% 48.82/6.55    spl16_12 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).
% 48.82/6.55  fof(f57461,plain,(
% 48.82/6.55    k1_xboole_0 = k7_setfam_1(sK0,sK1) | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) | (~spl16_574 | ~spl16_1139)),
% 48.82/6.55    inference(resolution,[],[f57454,f23271])).
% 48.82/6.55  fof(f23271,plain,(
% 48.82/6.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) ) | ~spl16_574),
% 48.82/6.55    inference(avatar_component_clause,[],[f23270])).
% 48.82/6.55  fof(f23270,plain,(
% 48.82/6.55    spl16_574 <=> ! [X1,X0] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_574])])).
% 48.82/6.55  fof(f57454,plain,(
% 48.82/6.55    r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0)) | ~spl16_1139),
% 48.82/6.55    inference(avatar_component_clause,[],[f57452])).
% 48.82/6.55  fof(f57452,plain,(
% 48.82/6.55    spl16_1139 <=> r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1139])])).
% 48.82/6.55  fof(f57455,plain,(
% 48.82/6.55    spl16_1139 | ~spl16_5 | ~spl16_577 | ~spl16_1049 | ~spl16_1136),
% 48.82/6.55    inference(avatar_split_clause,[],[f57442,f57416,f54602,f23479,f523,f57452])).
% 48.82/6.55  fof(f523,plain,(
% 48.82/6.55    spl16_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).
% 48.82/6.55  fof(f23479,plain,(
% 48.82/6.55    spl16_577 <=> ! [X7] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_577])])).
% 48.82/6.55  fof(f54602,plain,(
% 48.82/6.55    spl16_1049 <=> ! [X1,X0,X2] : (r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1049])])).
% 48.82/6.55  fof(f57416,plain,(
% 48.82/6.55    spl16_1136 <=> r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1136])])).
% 48.82/6.55  fof(f57442,plain,(
% 48.82/6.55    r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0)) | (~spl16_5 | ~spl16_577 | ~spl16_1049 | ~spl16_1136)),
% 48.82/6.55    inference(subsumption_resolution,[],[f57441,f525])).
% 48.82/6.55  fof(f525,plain,(
% 48.82/6.55    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl16_5),
% 48.82/6.55    inference(avatar_component_clause,[],[f523])).
% 48.82/6.55  fof(f57441,plain,(
% 48.82/6.55    r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl16_577 | ~spl16_1049 | ~spl16_1136)),
% 48.82/6.55    inference(subsumption_resolution,[],[f57423,f23480])).
% 48.82/6.55  fof(f23480,plain,(
% 48.82/6.55    ( ! [X7] : (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7)))) ) | ~spl16_577),
% 48.82/6.55    inference(avatar_component_clause,[],[f23479])).
% 48.82/6.55  fof(f57423,plain,(
% 48.82/6.55    r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0)) | ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl16_1049 | ~spl16_1136)),
% 48.82/6.55    inference(resolution,[],[f57418,f54603])).
% 48.82/6.55  fof(f54603,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,k7_setfam_1(X0,X2)) | r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl16_1049),
% 48.82/6.55    inference(avatar_component_clause,[],[f54602])).
% 48.82/6.55  fof(f57418,plain,(
% 48.82/6.55    r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) | ~spl16_1136),
% 48.82/6.55    inference(avatar_component_clause,[],[f57416])).
% 48.82/6.55  fof(f57419,plain,(
% 48.82/6.55    spl16_1136 | ~spl16_21 | ~spl16_1135),
% 48.82/6.55    inference(avatar_split_clause,[],[f57408,f57375,f898,f57416])).
% 48.82/6.55  fof(f898,plain,(
% 48.82/6.55    spl16_21 <=> ! [X19] : (r1_tarski(sK1,X19) | ~r2_hidden(sK0,X19))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_21])])).
% 48.82/6.55  fof(f57375,plain,(
% 48.82/6.55    spl16_1135 <=> ! [X36] : r2_hidden(X36,k7_setfam_1(X36,k1_tarski(k1_xboole_0)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1135])])).
% 48.82/6.55  fof(f57408,plain,(
% 48.82/6.55    r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) | (~spl16_21 | ~spl16_1135)),
% 48.82/6.55    inference(resolution,[],[f57376,f899])).
% 48.82/6.55  fof(f899,plain,(
% 48.82/6.55    ( ! [X19] : (~r2_hidden(sK0,X19) | r1_tarski(sK1,X19)) ) | ~spl16_21),
% 48.82/6.55    inference(avatar_component_clause,[],[f898])).
% 48.82/6.55  fof(f57376,plain,(
% 48.82/6.55    ( ! [X36] : (r2_hidden(X36,k7_setfam_1(X36,k1_tarski(k1_xboole_0)))) ) | ~spl16_1135),
% 48.82/6.55    inference(avatar_component_clause,[],[f57375])).
% 48.82/6.55  fof(f57377,plain,(
% 48.82/6.55    spl16_1135 | ~spl16_494 | ~spl16_577 | ~spl16_599 | ~spl16_823 | ~spl16_1007 | ~spl16_1121),
% 48.82/6.55    inference(avatar_split_clause,[],[f57368,f56506,f52930,f45635,f37849,f23479,f19241,f57375])).
% 48.82/6.55  fof(f19241,plain,(
% 48.82/6.55    spl16_494 <=> ! [X3,X0] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_494])])).
% 48.82/6.55  fof(f37849,plain,(
% 48.82/6.55    spl16_599 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_599])])).
% 48.82/6.55  fof(f45635,plain,(
% 48.82/6.55    spl16_823 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_823])])).
% 48.82/6.55  fof(f52930,plain,(
% 48.82/6.55    spl16_1007 <=> ! [X1,X0,X2] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1007])])).
% 48.82/6.55  fof(f56506,plain,(
% 48.82/6.55    spl16_1121 <=> ! [X10] : r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1121])])).
% 48.82/6.55  fof(f57368,plain,(
% 48.82/6.55    ( ! [X36] : (r2_hidden(X36,k7_setfam_1(X36,k1_tarski(k1_xboole_0)))) ) | (~spl16_494 | ~spl16_577 | ~spl16_599 | ~spl16_823 | ~spl16_1007 | ~spl16_1121)),
% 48.82/6.55    inference(forward_demodulation,[],[f57367,f46617])).
% 48.82/6.55  fof(f46617,plain,(
% 48.82/6.55    ( ! [X9] : (k3_subset_1(X9,k1_xboole_0) = X9) ) | (~spl16_599 | ~spl16_823)),
% 48.82/6.55    inference(forward_demodulation,[],[f46586,f237])).
% 48.82/6.55  fof(f237,plain,(
% 48.82/6.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 48.82/6.55    inference(cnf_transformation,[],[f27])).
% 48.82/6.55  fof(f27,axiom,(
% 48.82/6.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 48.82/6.55  fof(f46586,plain,(
% 48.82/6.55    ( ! [X9] : (k4_xboole_0(X9,k1_xboole_0) = k3_subset_1(X9,k1_xboole_0)) ) | (~spl16_599 | ~spl16_823)),
% 48.82/6.55    inference(resolution,[],[f45636,f37850])).
% 48.82/6.55  fof(f37850,plain,(
% 48.82/6.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl16_599),
% 48.82/6.55    inference(avatar_component_clause,[],[f37849])).
% 48.82/6.55  fof(f45636,plain,(
% 48.82/6.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl16_823),
% 48.82/6.55    inference(avatar_component_clause,[],[f45635])).
% 48.82/6.55  fof(f57367,plain,(
% 48.82/6.55    ( ! [X36] : (r2_hidden(k3_subset_1(X36,k1_xboole_0),k7_setfam_1(X36,k1_tarski(k1_xboole_0)))) ) | (~spl16_494 | ~spl16_577 | ~spl16_1007 | ~spl16_1121)),
% 48.82/6.55    inference(forward_demodulation,[],[f57366,f57244])).
% 48.82/6.55  fof(f57244,plain,(
% 48.82/6.55    ( ! [X7] : (k1_xboole_0 = sK5(k1_zfmisc_1(X7),k1_tarski(k1_xboole_0))) ) | (~spl16_494 | ~spl16_1121)),
% 48.82/6.55    inference(resolution,[],[f56507,f19242])).
% 48.82/6.55  fof(f19242,plain,(
% 48.82/6.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) ) | ~spl16_494),
% 48.82/6.55    inference(avatar_component_clause,[],[f19241])).
% 48.82/6.55  fof(f56507,plain,(
% 48.82/6.55    ( ! [X10] : (r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))) ) | ~spl16_1121),
% 48.82/6.55    inference(avatar_component_clause,[],[f56506])).
% 48.82/6.55  fof(f57366,plain,(
% 48.82/6.55    ( ! [X37,X36] : (r2_hidden(k3_subset_1(X36,sK5(k1_zfmisc_1(X37),k1_tarski(k1_xboole_0))),k7_setfam_1(X36,k1_tarski(k1_xboole_0)))) ) | (~spl16_577 | ~spl16_1007 | ~spl16_1121)),
% 48.82/6.55    inference(subsumption_resolution,[],[f57268,f23480])).
% 48.82/6.55  fof(f57268,plain,(
% 48.82/6.55    ( ! [X37,X36] : (r2_hidden(k3_subset_1(X36,sK5(k1_zfmisc_1(X37),k1_tarski(k1_xboole_0))),k7_setfam_1(X36,k1_tarski(k1_xboole_0))) | ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X36)))) ) | (~spl16_1007 | ~spl16_1121)),
% 48.82/6.55    inference(resolution,[],[f56507,f52931])).
% 48.82/6.55  fof(f52931,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl16_1007),
% 48.82/6.55    inference(avatar_component_clause,[],[f52930])).
% 48.82/6.55  fof(f56508,plain,(
% 48.82/6.55    spl16_1121 | ~spl16_63 | ~spl16_577 | ~spl16_873),
% 48.82/6.55    inference(avatar_split_clause,[],[f48960,f47811,f23479,f2133,f56506])).
% 48.82/6.55  fof(f2133,plain,(
% 48.82/6.55    spl16_63 <=> ! [X3] : k1_xboole_0 != k1_tarski(X3)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_63])])).
% 48.82/6.55  fof(f47811,plain,(
% 48.82/6.55    spl16_873 <=> ! [X1,X0] : (r2_hidden(sK5(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_873])])).
% 48.82/6.55  fof(f48960,plain,(
% 48.82/6.55    ( ! [X10] : (r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))) ) | (~spl16_63 | ~spl16_577 | ~spl16_873)),
% 48.82/6.55    inference(subsumption_resolution,[],[f48935,f2134])).
% 48.82/6.55  fof(f2134,plain,(
% 48.82/6.55    ( ! [X3] : (k1_xboole_0 != k1_tarski(X3)) ) | ~spl16_63),
% 48.82/6.55    inference(avatar_component_clause,[],[f2133])).
% 48.82/6.55  fof(f48935,plain,(
% 48.82/6.55    ( ! [X10] : (k1_xboole_0 = k1_tarski(k1_xboole_0) | r2_hidden(sK5(k1_zfmisc_1(X10),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))) ) | (~spl16_577 | ~spl16_873)),
% 48.82/6.55    inference(resolution,[],[f47812,f23480])).
% 48.82/6.55  fof(f47812,plain,(
% 48.82/6.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK5(X0,X1),X1)) ) | ~spl16_873),
% 48.82/6.55    inference(avatar_component_clause,[],[f47811])).
% 48.82/6.55  fof(f54604,plain,(
% 48.82/6.55    spl16_1049),
% 48.82/6.55    inference(avatar_split_clause,[],[f290,f54602])).
% 48.82/6.55  fof(f290,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f178])).
% 48.82/6.55  fof(f178,plain,(
% 48.82/6.55    ! [X0,X1] : (! [X2] : (((r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2))) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(nnf_transformation,[],[f134])).
% 48.82/6.55  fof(f134,plain,(
% 48.82/6.55    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(ennf_transformation,[],[f97])).
% 48.82/6.55  fof(f97,axiom,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).
% 48.82/6.55  fof(f52932,plain,(
% 48.82/6.55    spl16_1007),
% 48.82/6.55    inference(avatar_split_clause,[],[f37355,f52930])).
% 48.82/6.55  fof(f37355,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 48.82/6.55    inference(subsumption_resolution,[],[f281,f350])).
% 48.82/6.55  fof(f350,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f155])).
% 48.82/6.55  fof(f155,plain,(
% 48.82/6.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 48.82/6.55    inference(flattening,[],[f154])).
% 48.82/6.55  fof(f154,plain,(
% 48.82/6.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 48.82/6.55    inference(ennf_transformation,[],[f95])).
% 48.82/6.55  fof(f95,axiom,(
% 48.82/6.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 48.82/6.55  fof(f281,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f172])).
% 48.82/6.55  fof(f172,plain,(
% 48.82/6.55    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(nnf_transformation,[],[f128])).
% 48.82/6.55  fof(f128,plain,(
% 48.82/6.55    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(ennf_transformation,[],[f94])).
% 48.82/6.55  fof(f94,axiom,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 48.82/6.55  fof(f47813,plain,(
% 48.82/6.55    spl16_873),
% 48.82/6.55    inference(avatar_split_clause,[],[f275,f47811])).
% 48.82/6.55  fof(f275,plain,(
% 48.82/6.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f171])).
% 48.82/6.55  fof(f171,plain,(
% 48.82/6.55    ! [X0,X1] : ((r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 48.82/6.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f122,f170])).
% 48.82/6.55  fof(f170,plain,(
% 48.82/6.55    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)))),
% 48.82/6.55    introduced(choice_axiom,[])).
% 48.82/6.55  fof(f122,plain,(
% 48.82/6.55    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 48.82/6.55    inference(flattening,[],[f121])).
% 48.82/6.55  fof(f121,plain,(
% 48.82/6.55    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 48.82/6.55    inference(ennf_transformation,[],[f84])).
% 48.82/6.55  fof(f84,axiom,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 48.82/6.55  fof(f45637,plain,(
% 48.82/6.55    spl16_823),
% 48.82/6.55    inference(avatar_split_clause,[],[f272,f45635])).
% 48.82/6.55  fof(f272,plain,(
% 48.82/6.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f119])).
% 48.82/6.55  fof(f119,plain,(
% 48.82/6.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 48.82/6.55    inference(ennf_transformation,[],[f79])).
% 48.82/6.55  fof(f79,axiom,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 48.82/6.55  fof(f37851,plain,(
% 48.82/6.55    spl16_599),
% 48.82/6.55    inference(avatar_split_clause,[],[f235,f37849])).
% 48.82/6.55  fof(f235,plain,(
% 48.82/6.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f85])).
% 48.82/6.55  fof(f85,axiom,(
% 48.82/6.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 48.82/6.55  fof(f23481,plain,(
% 48.82/6.55    spl16_577 | ~spl16_270 | ~spl16_570),
% 48.82/6.55    inference(avatar_split_clause,[],[f23430,f22960,f8405,f23479])).
% 48.82/6.55  fof(f8405,plain,(
% 48.82/6.55    spl16_270 <=> ! [X0] : k1_xboole_0 != k1_zfmisc_1(X0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_270])])).
% 48.82/6.55  fof(f22960,plain,(
% 48.82/6.55    spl16_570 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_570])])).
% 48.82/6.55  fof(f23430,plain,(
% 48.82/6.55    ( ! [X7] : (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7)))) ) | (~spl16_270 | ~spl16_570)),
% 48.82/6.55    inference(subsumption_resolution,[],[f23387,f8406])).
% 48.82/6.55  fof(f8406,plain,(
% 48.82/6.55    ( ! [X0] : (k1_xboole_0 != k1_zfmisc_1(X0)) ) | ~spl16_270),
% 48.82/6.55    inference(avatar_component_clause,[],[f8405])).
% 48.82/6.55  fof(f23387,plain,(
% 48.82/6.55    ( ! [X7] : (k1_xboole_0 = k1_zfmisc_1(X7) | m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X7)))) ) | ~spl16_570),
% 48.82/6.55    inference(resolution,[],[f22961,f235])).
% 48.82/6.55  fof(f22961,plain,(
% 48.82/6.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) ) | ~spl16_570),
% 48.82/6.55    inference(avatar_component_clause,[],[f22960])).
% 48.82/6.55  fof(f23272,plain,(
% 48.82/6.55    spl16_574),
% 48.82/6.55    inference(avatar_split_clause,[],[f314,f23270])).
% 48.82/6.55  fof(f314,plain,(
% 48.82/6.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f196])).
% 48.82/6.55  fof(f196,plain,(
% 48.82/6.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 48.82/6.55    inference(flattening,[],[f195])).
% 48.82/6.55  fof(f195,plain,(
% 48.82/6.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 48.82/6.55    inference(nnf_transformation,[],[f60])).
% 48.82/6.55  fof(f60,axiom,(
% 48.82/6.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 48.82/6.55  fof(f22962,plain,(
% 48.82/6.55    spl16_570),
% 48.82/6.55    inference(avatar_split_clause,[],[f264,f22960])).
% 48.82/6.55  fof(f264,plain,(
% 48.82/6.55    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f111])).
% 48.82/6.55  fof(f111,plain,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 48.82/6.55    inference(flattening,[],[f110])).
% 48.82/6.55  fof(f110,plain,(
% 48.82/6.55    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 48.82/6.55    inference(ennf_transformation,[],[f86])).
% 48.82/6.55  fof(f86,axiom,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 48.82/6.55  fof(f19243,plain,(
% 48.82/6.55    spl16_494),
% 48.82/6.55    inference(avatar_split_clause,[],[f391,f19241])).
% 48.82/6.55  fof(f391,plain,(
% 48.82/6.55    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 48.82/6.55    inference(equality_resolution,[],[f304])).
% 48.82/6.55  fof(f304,plain,(
% 48.82/6.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 48.82/6.55    inference(cnf_transformation,[],[f189])).
% 48.82/6.55  fof(f189,plain,(
% 48.82/6.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 48.82/6.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f187,f188])).
% 48.82/6.55  fof(f188,plain,(
% 48.82/6.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1))))),
% 48.82/6.55    introduced(choice_axiom,[])).
% 48.82/6.55  fof(f187,plain,(
% 48.82/6.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 48.82/6.55    inference(rectify,[],[f186])).
% 48.82/6.55  fof(f186,plain,(
% 48.82/6.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 48.82/6.55    inference(nnf_transformation,[],[f47])).
% 48.82/6.55  fof(f47,axiom,(
% 48.82/6.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 48.82/6.55  fof(f8407,plain,(
% 48.82/6.55    spl16_270 | ~spl16_268),
% 48.82/6.55    inference(avatar_split_clause,[],[f8392,f8366,f8405])).
% 48.82/6.55  fof(f8366,plain,(
% 48.82/6.55    spl16_268 <=> ! [X5] : k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(X5),k1_xboole_0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_268])])).
% 48.82/6.55  fof(f8392,plain,(
% 48.82/6.55    ( ! [X0] : (k1_xboole_0 != k1_zfmisc_1(X0)) ) | ~spl16_268),
% 48.82/6.55    inference(superposition,[],[f8367,f237])).
% 48.82/6.55  fof(f8367,plain,(
% 48.82/6.55    ( ! [X5] : (k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(X5),k1_xboole_0)) ) | ~spl16_268),
% 48.82/6.55    inference(avatar_component_clause,[],[f8366])).
% 48.82/6.55  fof(f8368,plain,(
% 48.82/6.55    spl16_268 | ~spl16_266),
% 48.82/6.55    inference(avatar_split_clause,[],[f8245,f8238,f8366])).
% 48.82/6.55  fof(f8238,plain,(
% 48.82/6.55    spl16_266 <=> ! [X7] : ~r1_tarski(k1_zfmisc_1(X7),k1_xboole_0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_266])])).
% 48.82/6.55  fof(f8245,plain,(
% 48.82/6.55    ( ! [X5] : (k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(X5),k1_xboole_0)) ) | ~spl16_266),
% 48.82/6.55    inference(resolution,[],[f8239,f319])).
% 48.82/6.55  fof(f319,plain,(
% 48.82/6.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 48.82/6.55    inference(cnf_transformation,[],[f198])).
% 48.82/6.55  fof(f198,plain,(
% 48.82/6.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 48.82/6.55    inference(nnf_transformation,[],[f25])).
% 48.82/6.55  fof(f25,axiom,(
% 48.82/6.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 48.82/6.55  fof(f8239,plain,(
% 48.82/6.55    ( ! [X7] : (~r1_tarski(k1_zfmisc_1(X7),k1_xboole_0)) ) | ~spl16_266),
% 48.82/6.55    inference(avatar_component_clause,[],[f8238])).
% 48.82/6.55  fof(f8240,plain,(
% 48.82/6.55    spl16_266 | ~spl16_240),
% 48.82/6.55    inference(avatar_split_clause,[],[f8210,f7614,f8238])).
% 48.82/6.55  fof(f7614,plain,(
% 48.82/6.55    spl16_240 <=> ! [X9,X10] : (~r1_tarski(X10,k1_xboole_0) | ~r1_tarski(k1_tarski(X9),X10))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_240])])).
% 48.82/6.55  fof(f8210,plain,(
% 48.82/6.55    ( ! [X7] : (~r1_tarski(k1_zfmisc_1(X7),k1_xboole_0)) ) | ~spl16_240),
% 48.82/6.55    inference(resolution,[],[f7615,f239])).
% 48.82/6.55  fof(f239,plain,(
% 48.82/6.55    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f76])).
% 48.82/6.55  fof(f76,axiom,(
% 48.82/6.55    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 48.82/6.55  fof(f7615,plain,(
% 48.82/6.55    ( ! [X10,X9] : (~r1_tarski(k1_tarski(X9),X10) | ~r1_tarski(X10,k1_xboole_0)) ) | ~spl16_240),
% 48.82/6.55    inference(avatar_component_clause,[],[f7614])).
% 48.82/6.55  fof(f7616,plain,(
% 48.82/6.55    spl16_240 | ~spl16_52),
% 48.82/6.55    inference(avatar_split_clause,[],[f1681,f1666,f7614])).
% 48.82/6.55  fof(f1666,plain,(
% 48.82/6.55    spl16_52 <=> ! [X60] : ~r1_tarski(k1_tarski(X60),k1_xboole_0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).
% 48.82/6.55  fof(f1681,plain,(
% 48.82/6.55    ( ! [X10,X9] : (~r1_tarski(X10,k1_xboole_0) | ~r1_tarski(k1_tarski(X9),X10)) ) | ~spl16_52),
% 48.82/6.55    inference(resolution,[],[f1667,f351])).
% 48.82/6.55  fof(f351,plain,(
% 48.82/6.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f157])).
% 48.82/6.55  fof(f157,plain,(
% 48.82/6.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 48.82/6.55    inference(flattening,[],[f156])).
% 48.82/6.55  fof(f156,plain,(
% 48.82/6.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 48.82/6.55    inference(ennf_transformation,[],[f17])).
% 48.82/6.55  fof(f17,axiom,(
% 48.82/6.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 48.82/6.55  fof(f1667,plain,(
% 48.82/6.55    ( ! [X60] : (~r1_tarski(k1_tarski(X60),k1_xboole_0)) ) | ~spl16_52),
% 48.82/6.55    inference(avatar_component_clause,[],[f1666])).
% 48.82/6.55  fof(f2135,plain,(
% 48.82/6.55    spl16_63 | ~spl16_47),
% 48.82/6.55    inference(avatar_split_clause,[],[f2131,f1566,f2133])).
% 48.82/6.55  fof(f1566,plain,(
% 48.82/6.55    spl16_47 <=> ! [X9] : k1_xboole_0 != k4_xboole_0(k1_tarski(X9),k1_xboole_0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_47])])).
% 48.82/6.55  fof(f2131,plain,(
% 48.82/6.55    ( ! [X3] : (k1_xboole_0 != k1_tarski(X3)) ) | ~spl16_47),
% 48.82/6.55    inference(subsumption_resolution,[],[f2124,f1567])).
% 48.82/6.55  fof(f1567,plain,(
% 48.82/6.55    ( ! [X9] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X9),k1_xboole_0)) ) | ~spl16_47),
% 48.82/6.55    inference(avatar_component_clause,[],[f1566])).
% 48.82/6.55  fof(f2124,plain,(
% 48.82/6.55    ( ! [X3] : (k1_xboole_0 != k1_tarski(X3) | k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_xboole_0)) ) | ~spl16_47),
% 48.82/6.55    inference(superposition,[],[f1567,f262])).
% 48.82/6.55  fof(f262,plain,(
% 48.82/6.55    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f72])).
% 48.82/6.55  fof(f72,axiom,(
% 48.82/6.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 48.82/6.55  fof(f1668,plain,(
% 48.82/6.55    spl16_52 | ~spl16_45),
% 48.82/6.55    inference(avatar_split_clause,[],[f1599,f1557,f1666])).
% 48.82/6.55  fof(f1557,plain,(
% 48.82/6.55    spl16_45 <=> ! [X7,X6] : (~r2_hidden(X6,X7) | ~r1_tarski(X7,k1_xboole_0))),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).
% 48.82/6.55  fof(f1599,plain,(
% 48.82/6.55    ( ! [X60] : (~r1_tarski(k1_tarski(X60),k1_xboole_0)) ) | ~spl16_45),
% 48.82/6.55    inference(resolution,[],[f1558,f390])).
% 48.82/6.55  fof(f390,plain,(
% 48.82/6.55    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 48.82/6.55    inference(equality_resolution,[],[f389])).
% 48.82/6.55  fof(f389,plain,(
% 48.82/6.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 48.82/6.55    inference(equality_resolution,[],[f305])).
% 48.82/6.55  fof(f305,plain,(
% 48.82/6.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 48.82/6.55    inference(cnf_transformation,[],[f189])).
% 48.82/6.55  fof(f1558,plain,(
% 48.82/6.55    ( ! [X6,X7] : (~r2_hidden(X6,X7) | ~r1_tarski(X7,k1_xboole_0)) ) | ~spl16_45),
% 48.82/6.55    inference(avatar_component_clause,[],[f1557])).
% 48.82/6.55  fof(f1568,plain,(
% 48.82/6.55    spl16_47 | ~spl16_16),
% 48.82/6.55    inference(avatar_split_clause,[],[f798,f789,f1566])).
% 48.82/6.55  fof(f789,plain,(
% 48.82/6.55    spl16_16 <=> ! [X12] : ~r2_hidden(X12,k1_xboole_0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).
% 48.82/6.55  fof(f798,plain,(
% 48.82/6.55    ( ! [X9] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X9),k1_xboole_0)) ) | ~spl16_16),
% 48.82/6.55    inference(resolution,[],[f790,f321])).
% 48.82/6.55  fof(f321,plain,(
% 48.82/6.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f199])).
% 48.82/6.55  fof(f199,plain,(
% 48.82/6.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 48.82/6.55    inference(nnf_transformation,[],[f71])).
% 48.82/6.55  fof(f71,axiom,(
% 48.82/6.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 48.82/6.55  fof(f790,plain,(
% 48.82/6.55    ( ! [X12] : (~r2_hidden(X12,k1_xboole_0)) ) | ~spl16_16),
% 48.82/6.55    inference(avatar_component_clause,[],[f789])).
% 48.82/6.55  fof(f1559,plain,(
% 48.82/6.55    spl16_45 | ~spl16_16),
% 48.82/6.55    inference(avatar_split_clause,[],[f796,f789,f1557])).
% 48.82/6.55  fof(f796,plain,(
% 48.82/6.55    ( ! [X6,X7] : (~r2_hidden(X6,X7) | ~r1_tarski(X7,k1_xboole_0)) ) | ~spl16_16),
% 48.82/6.55    inference(resolution,[],[f790,f301])).
% 48.82/6.55  fof(f301,plain,(
% 48.82/6.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f185])).
% 48.82/6.55  fof(f185,plain,(
% 48.82/6.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 48.82/6.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f183,f184])).
% 48.82/6.55  fof(f184,plain,(
% 48.82/6.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 48.82/6.55    introduced(choice_axiom,[])).
% 48.82/6.55  fof(f183,plain,(
% 48.82/6.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 48.82/6.55    inference(rectify,[],[f182])).
% 48.82/6.55  fof(f182,plain,(
% 48.82/6.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 48.82/6.55    inference(nnf_transformation,[],[f140])).
% 48.82/6.55  fof(f140,plain,(
% 48.82/6.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 48.82/6.55    inference(ennf_transformation,[],[f3])).
% 48.82/6.55  fof(f3,axiom,(
% 48.82/6.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 48.82/6.55  fof(f900,plain,(
% 48.82/6.55    spl16_21 | ~spl16_1),
% 48.82/6.55    inference(avatar_split_clause,[],[f448,f414,f898])).
% 48.82/6.55  fof(f414,plain,(
% 48.82/6.55    spl16_1 <=> sK1 = k1_tarski(sK0)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 48.82/6.55  fof(f448,plain,(
% 48.82/6.55    ( ! [X19] : (r1_tarski(sK1,X19) | ~r2_hidden(sK0,X19)) ) | ~spl16_1),
% 48.82/6.55    inference(superposition,[],[f318,f416])).
% 48.82/6.55  fof(f416,plain,(
% 48.82/6.55    sK1 = k1_tarski(sK0) | ~spl16_1),
% 48.82/6.55    inference(avatar_component_clause,[],[f414])).
% 48.82/6.55  fof(f318,plain,(
% 48.82/6.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f197])).
% 48.82/6.55  fof(f197,plain,(
% 48.82/6.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 48.82/6.55    inference(nnf_transformation,[],[f59])).
% 48.82/6.55  fof(f59,axiom,(
% 48.82/6.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 48.82/6.55  fof(f791,plain,(
% 48.82/6.55    spl16_16 | ~spl16_14),
% 48.82/6.55    inference(avatar_split_clause,[],[f787,f749,f789])).
% 48.82/6.55  fof(f749,plain,(
% 48.82/6.55    spl16_14 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).
% 48.82/6.55  fof(f787,plain,(
% 48.82/6.55    ( ! [X12] : (~r2_hidden(X12,k1_xboole_0)) ) | ~spl16_14),
% 48.82/6.55    inference(subsumption_resolution,[],[f781,f780])).
% 48.82/6.55  fof(f780,plain,(
% 48.82/6.55    ( ! [X11] : (~r2_hidden(X11,k1_xboole_0) | ~r2_hidden(X11,sK1)) ) | ~spl16_14),
% 48.82/6.55    inference(superposition,[],[f403,f751])).
% 48.82/6.55  fof(f751,plain,(
% 48.82/6.55    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl16_14),
% 48.82/6.55    inference(avatar_component_clause,[],[f749])).
% 48.82/6.55  fof(f403,plain,(
% 48.82/6.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 48.82/6.55    inference(equality_resolution,[],[f360])).
% 48.82/6.55  fof(f360,plain,(
% 48.82/6.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 48.82/6.55    inference(cnf_transformation,[],[f217])).
% 48.82/6.55  fof(f217,plain,(
% 48.82/6.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK14(X0,X1,X2),X1) | ~r2_hidden(sK14(X0,X1,X2),X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & ((~r2_hidden(sK14(X0,X1,X2),X1) & r2_hidden(sK14(X0,X1,X2),X0)) | r2_hidden(sK14(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 48.82/6.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f215,f216])).
% 48.82/6.55  fof(f216,plain,(
% 48.82/6.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK14(X0,X1,X2),X1) | ~r2_hidden(sK14(X0,X1,X2),X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & ((~r2_hidden(sK14(X0,X1,X2),X1) & r2_hidden(sK14(X0,X1,X2),X0)) | r2_hidden(sK14(X0,X1,X2),X2))))),
% 48.82/6.55    introduced(choice_axiom,[])).
% 48.82/6.55  fof(f215,plain,(
% 48.82/6.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 48.82/6.55    inference(rectify,[],[f214])).
% 48.82/6.55  fof(f214,plain,(
% 48.82/6.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 48.82/6.55    inference(flattening,[],[f213])).
% 48.82/6.55  fof(f213,plain,(
% 48.82/6.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 48.82/6.55    inference(nnf_transformation,[],[f5])).
% 48.82/6.55  fof(f5,axiom,(
% 48.82/6.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 48.82/6.55  fof(f781,plain,(
% 48.82/6.55    ( ! [X12] : (~r2_hidden(X12,k1_xboole_0) | r2_hidden(X12,sK1)) ) | ~spl16_14),
% 48.82/6.55    inference(superposition,[],[f404,f751])).
% 48.82/6.55  fof(f404,plain,(
% 48.82/6.55    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 48.82/6.55    inference(equality_resolution,[],[f359])).
% 48.82/6.55  fof(f359,plain,(
% 48.82/6.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 48.82/6.55    inference(cnf_transformation,[],[f217])).
% 48.82/6.55  fof(f752,plain,(
% 48.82/6.55    spl16_14 | ~spl16_1 | ~spl16_2),
% 48.82/6.55    inference(avatar_split_clause,[],[f508,f475,f414,f749])).
% 48.82/6.55  fof(f475,plain,(
% 48.82/6.55    spl16_2 <=> r2_hidden(sK0,sK1)),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 48.82/6.55  fof(f508,plain,(
% 48.82/6.55    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl16_1 | ~spl16_2)),
% 48.82/6.55    inference(forward_demodulation,[],[f493,f416])).
% 48.82/6.55  fof(f493,plain,(
% 48.82/6.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl16_2),
% 48.82/6.55    inference(resolution,[],[f477,f322])).
% 48.82/6.55  fof(f322,plain,(
% 48.82/6.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 48.82/6.55    inference(cnf_transformation,[],[f199])).
% 48.82/6.55  fof(f477,plain,(
% 48.82/6.55    r2_hidden(sK0,sK1) | ~spl16_2),
% 48.82/6.55    inference(avatar_component_clause,[],[f475])).
% 48.82/6.55  fof(f614,plain,(
% 48.82/6.55    ~spl16_12 | spl16_4 | ~spl16_5),
% 48.82/6.55    inference(avatar_split_clause,[],[f587,f523,f518,f611])).
% 48.82/6.55  fof(f518,plain,(
% 48.82/6.55    spl16_4 <=> k1_xboole_0 = sK1),
% 48.82/6.55    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 48.82/6.55  fof(f587,plain,(
% 48.82/6.55    k1_xboole_0 != k7_setfam_1(sK0,sK1) | (spl16_4 | ~spl16_5)),
% 48.82/6.55    inference(subsumption_resolution,[],[f551,f520])).
% 48.82/6.55  fof(f520,plain,(
% 48.82/6.55    k1_xboole_0 != sK1 | spl16_4),
% 48.82/6.55    inference(avatar_component_clause,[],[f518])).
% 48.82/6.55  fof(f551,plain,(
% 48.82/6.55    k1_xboole_0 != k7_setfam_1(sK0,sK1) | k1_xboole_0 = sK1 | ~spl16_5),
% 48.82/6.55    inference(resolution,[],[f525,f279])).
% 48.82/6.55  fof(f279,plain,(
% 48.82/6.55    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 48.82/6.55    inference(cnf_transformation,[],[f127])).
% 48.82/6.55  fof(f127,plain,(
% 48.82/6.55    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(flattening,[],[f126])).
% 48.82/6.55  fof(f126,plain,(
% 48.82/6.55    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(ennf_transformation,[],[f93])).
% 48.82/6.55  fof(f93,axiom,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 48.82/6.55  fof(f597,plain,(
% 48.82/6.55    ~spl16_8),
% 48.82/6.55    inference(avatar_split_clause,[],[f231,f594])).
% 48.82/6.55  fof(f231,plain,(
% 48.82/6.55    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 48.82/6.55    inference(cnf_transformation,[],[f163])).
% 48.82/6.55  fof(f163,plain,(
% 48.82/6.55    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) & sK1 = k1_tarski(sK0) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 48.82/6.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f104,f162])).
% 48.82/6.55  fof(f162,plain,(
% 48.82/6.55    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) & sK1 = k1_tarski(sK0) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 48.82/6.55    introduced(choice_axiom,[])).
% 48.82/6.55  fof(f104,plain,(
% 48.82/6.55    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(flattening,[],[f103])).
% 48.82/6.55  fof(f103,plain,(
% 48.82/6.55    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 48.82/6.55    inference(ennf_transformation,[],[f100])).
% 48.82/6.55  fof(f100,negated_conjecture,(
% 48.82/6.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 48.82/6.55    inference(negated_conjecture,[],[f99])).
% 48.82/6.55  fof(f99,conjecture,(
% 48.82/6.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).
% 48.82/6.55  fof(f526,plain,(
% 48.82/6.55    spl16_5),
% 48.82/6.55    inference(avatar_split_clause,[],[f229,f523])).
% 48.82/6.55  fof(f229,plain,(
% 48.82/6.55    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 48.82/6.55    inference(cnf_transformation,[],[f163])).
% 48.82/6.55  fof(f521,plain,(
% 48.82/6.55    ~spl16_4 | ~spl16_1 | ~spl16_2),
% 48.82/6.55    inference(avatar_split_clause,[],[f510,f475,f414,f518])).
% 48.82/6.55  fof(f510,plain,(
% 48.82/6.55    k1_xboole_0 != sK1 | (~spl16_1 | ~spl16_2)),
% 48.82/6.55    inference(forward_demodulation,[],[f509,f508])).
% 48.82/6.55  fof(f509,plain,(
% 48.82/6.55    sK1 != k4_xboole_0(sK1,sK1) | (~spl16_1 | ~spl16_2)),
% 48.82/6.55    inference(forward_demodulation,[],[f494,f416])).
% 48.82/6.55  fof(f494,plain,(
% 48.82/6.55    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl16_2),
% 48.82/6.55    inference(resolution,[],[f477,f323])).
% 48.82/6.55  fof(f323,plain,(
% 48.82/6.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 48.82/6.55    inference(cnf_transformation,[],[f200])).
% 48.82/6.55  fof(f200,plain,(
% 48.82/6.55    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 48.82/6.55    inference(nnf_transformation,[],[f68])).
% 48.82/6.55  fof(f68,axiom,(
% 48.82/6.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 48.82/6.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 48.82/6.55  fof(f478,plain,(
% 48.82/6.55    spl16_2 | ~spl16_1),
% 48.82/6.55    inference(avatar_split_clause,[],[f466,f414,f475])).
% 48.82/6.55  fof(f466,plain,(
% 48.82/6.55    r2_hidden(sK0,sK1) | ~spl16_1),
% 48.82/6.55    inference(superposition,[],[f390,f416])).
% 48.82/6.55  fof(f417,plain,(
% 48.82/6.55    spl16_1),
% 48.82/6.55    inference(avatar_split_clause,[],[f230,f414])).
% 48.82/6.55  fof(f230,plain,(
% 48.82/6.55    sK1 = k1_tarski(sK0)),
% 48.82/6.55    inference(cnf_transformation,[],[f163])).
% 48.82/6.55  % SZS output end Proof for theBenchmark
% 48.82/6.55  % (12715)------------------------------
% 48.82/6.55  % (12715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 48.82/6.55  % (12715)Termination reason: Refutation
% 48.82/6.55  
% 48.82/6.55  % (12715)Memory used [KB]: 44263
% 48.82/6.55  % (12715)Time elapsed: 3.758 s
% 48.82/6.55  % (12715)------------------------------
% 48.82/6.55  % (12715)------------------------------
% 49.47/6.57  % (12329)Success in time 6.201 s
%------------------------------------------------------------------------------
