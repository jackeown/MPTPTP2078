%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0321+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 8.65s
% Output     : Refutation 8.65s
% Verified   : 
% Statistics : Number of formulae       :  612 (1656 expanded)
%              Number of leaves         :  138 ( 791 expanded)
%              Depth                    :    8
%              Number of atoms          : 1547 (3788 expanded)
%              Number of equality atoms :  242 (1046 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7590,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f981,f986,f991,f1000,f1005,f1011,f1016,f1021,f1079,f1084,f1203,f1290,f1291,f1300,f1301,f1310,f1311,f1320,f1321,f1328,f1371,f1409,f1417,f1581,f1626,f1635,f1698,f1708,f1713,f1727,f1728,f1734,f1744,f1779,f1817,f1847,f2015,f2133,f2142,f2227,f3372,f3379,f3386,f3393,f3401,f3415,f3419,f3448,f3454,f3460,f3465,f3470,f3476,f3481,f3505,f3523,f3527,f3528,f3529,f3530,f3531,f3532,f3533,f3570,f3572,f3578,f3583,f3588,f3594,f3599,f3605,f3610,f3613,f3723,f3724,f4008,f4017,f4026,f4027,f4043,f4061,f4201,f4638,f4650,f4770,f4771,f4772,f4773,f4840,f4845,f4850,f4855,f4860,f4865,f4870,f4871,f4872,f4877,f4878,f4879,f4880,f4887,f4888,f4889,f4893,f4894,f4895,f4896,f4897,f4898,f4899,f4947,f4952,f4960,f4967,f4973,f4990,f4993,f5022,f5027,f5531,f5532,f5533,f5534,f5606,f5611,f5616,f5621,f5622,f5623,f5624,f5625,f5636,f5641,f5654,f5663,f5672,f5673,f6365,f6779,f7192,f7193,f7316,f7569,f7570,f7587,f7588,f7589])).

fof(f7589,plain,
    ( spl34_2
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(avatar_split_clause,[],[f7580,f3374,f997,f983])).

fof(f983,plain,
    ( spl34_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_2])])).

fof(f997,plain,
    ( spl34_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_5])])).

fof(f3374,plain,
    ( spl34_47
  <=> ! [X3] : ~ r2_hidden(X3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_47])])).

fof(f7580,plain,
    ( k1_xboole_0 = sK0
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(resolution,[],[f7571,f578])).

fof(f578,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f449])).

fof(f449,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f7571,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK0)
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(forward_demodulation,[],[f3375,f998])).

fof(f998,plain,
    ( sK0 = sK2
    | ~ spl34_5 ),
    inference(avatar_component_clause,[],[f997])).

fof(f3375,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK2)
    | ~ spl34_47 ),
    inference(avatar_component_clause,[],[f3374])).

fof(f7588,plain,
    ( spl34_92
    | spl34_2
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(avatar_split_clause,[],[f7579,f3374,f997,f983,f5529])).

fof(f5529,plain,
    ( spl34_92
  <=> ! [X0] : k2_tarski(X0,X0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_92])])).

fof(f7579,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK0
        | sK0 = k2_tarski(X1,X1) )
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(resolution,[],[f7571,f810])).

fof(f810,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f545,f729])).

fof(f729,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f545,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f441])).

fof(f441,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f309])).

fof(f309,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f7587,plain,
    ( spl34_92
    | spl34_2
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(avatar_split_clause,[],[f7578,f3374,f997,f983,f5529])).

fof(f7578,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | k2_tarski(X0,X0) = sK0 )
    | ~ spl34_5
    | ~ spl34_47 ),
    inference(resolution,[],[f7571,f808])).

fof(f808,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f543,f729])).

fof(f543,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f440])).

fof(f440,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f375])).

fof(f375,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f7570,plain,
    ( ~ spl34_102
    | ~ spl34_50
    | spl34_101 ),
    inference(avatar_split_clause,[],[f7567,f5656,f3384,f5660])).

fof(f5660,plain,
    ( spl34_102
  <=> r2_hidden(sK19(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_102])])).

fof(f3384,plain,
    ( spl34_50
  <=> ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_50])])).

fof(f5656,plain,
    ( spl34_101
  <=> r2_hidden(sK19(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_101])])).

fof(f7567,plain,
    ( ~ r2_hidden(sK19(sK3,sK1),sK1)
    | ~ spl34_50
    | spl34_101 ),
    inference(resolution,[],[f3385,f5658])).

fof(f5658,plain,
    ( ~ r2_hidden(sK19(sK3,sK1),sK3)
    | spl34_101 ),
    inference(avatar_component_clause,[],[f5656])).

fof(f3385,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK3)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl34_50 ),
    inference(avatar_component_clause,[],[f3384])).

fof(f7569,plain,
    ( ~ spl34_99
    | ~ spl34_50
    | spl34_100 ),
    inference(avatar_split_clause,[],[f7566,f5651,f3384,f5647])).

fof(f5647,plain,
    ( spl34_99
  <=> r2_hidden(sK19(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_99])])).

fof(f5651,plain,
    ( spl34_100
  <=> r2_hidden(sK19(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_100])])).

fof(f7566,plain,
    ( ~ r2_hidden(sK19(sK1,sK3),sK1)
    | ~ spl34_50
    | spl34_100 ),
    inference(resolution,[],[f3385,f5653])).

fof(f5653,plain,
    ( ~ r2_hidden(sK19(sK1,sK3),sK3)
    | spl34_100 ),
    inference(avatar_component_clause,[],[f5651])).

fof(f7316,plain,
    ( spl34_4
    | spl34_99
    | spl34_100 ),
    inference(avatar_split_clause,[],[f7315,f5651,f5647,f993])).

fof(f993,plain,
    ( spl34_4
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_4])])).

fof(f7315,plain,
    ( r2_hidden(sK19(sK1,sK3),sK1)
    | sK1 = sK3
    | spl34_100 ),
    inference(resolution,[],[f5653,f695])).

fof(f695,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK19(X0,X1),X1)
      | r2_hidden(sK19(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f477])).

fof(f477,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f7193,plain,
    ( ~ spl34_101
    | ~ spl34_48
    | spl34_102 ),
    inference(avatar_split_clause,[],[f7190,f5660,f3377,f5656])).

fof(f3377,plain,
    ( spl34_48
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK3)
        | r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_48])])).

fof(f7190,plain,
    ( ~ r2_hidden(sK19(sK3,sK1),sK3)
    | ~ spl34_48
    | spl34_102 ),
    inference(resolution,[],[f3378,f5662])).

fof(f5662,plain,
    ( ~ r2_hidden(sK19(sK3,sK1),sK1)
    | spl34_102 ),
    inference(avatar_component_clause,[],[f5660])).

fof(f3378,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(X2,sK3) )
    | ~ spl34_48 ),
    inference(avatar_component_clause,[],[f3377])).

fof(f7192,plain,
    ( ~ spl34_100
    | ~ spl34_48
    | spl34_99 ),
    inference(avatar_split_clause,[],[f7189,f5647,f3377,f5651])).

fof(f7189,plain,
    ( ~ r2_hidden(sK19(sK1,sK3),sK3)
    | ~ spl34_48
    | spl34_99 ),
    inference(resolution,[],[f3378,f5649])).

fof(f5649,plain,
    ( ~ r2_hidden(sK19(sK1,sK3),sK1)
    | spl34_99 ),
    inference(avatar_component_clause,[],[f5647])).

fof(f6779,plain,(
    ~ spl34_98 ),
    inference(avatar_contradiction_clause,[],[f6777])).

fof(f6777,plain,
    ( $false
    | ~ spl34_98 ),
    inference(resolution,[],[f5640,f1646])).

fof(f1646,plain,(
    ! [X2,X1] : ~ sP31(X2,k1_xboole_0,X1) ),
    inference(global_subsumption,[],[f1147,f1644])).

fof(f1644,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ sP31(X2,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f975,f943])).

fof(f943,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f558])).

fof(f558,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f323])).

fof(f323,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f975,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP31(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f770])).

fof(f770,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP31(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f285])).

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

fof(f1147,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f952,f1006])).

fof(f1006,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f831,f588])).

fof(f588,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f831,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f592,f719])).

fof(f719,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f592,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f952,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f844])).

fof(f844,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f617,f729])).

fof(f617,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f396])).

fof(f396,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f5640,plain,
    ( sP31(sK7(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl34_98 ),
    inference(avatar_component_clause,[],[f5638])).

fof(f5638,plain,
    ( spl34_98
  <=> sP31(sK7(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_98])])).

fof(f6365,plain,
    ( spl34_4
    | spl34_101
    | spl34_102 ),
    inference(avatar_split_clause,[],[f6364,f5660,f5656,f993])).

fof(f6364,plain,
    ( r2_hidden(sK19(sK3,sK1),sK3)
    | sK1 = sK3
    | spl34_102 ),
    inference(resolution,[],[f5662,f695])).

fof(f5673,plain,
    ( ~ spl34_104
    | ~ spl34_103
    | spl34_4 ),
    inference(avatar_split_clause,[],[f5645,f993,f5665,f5669])).

fof(f5669,plain,
    ( spl34_104
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_104])])).

fof(f5665,plain,
    ( spl34_103
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_103])])).

fof(f5645,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK3,sK1)
    | spl34_4 ),
    inference(extensionality_resolution,[],[f694,f995])).

fof(f995,plain,
    ( sK1 != sK3
    | spl34_4 ),
    inference(avatar_component_clause,[],[f993])).

fof(f694,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5672,plain,
    ( ~ spl34_103
    | ~ spl34_104
    | spl34_4 ),
    inference(avatar_split_clause,[],[f5644,f993,f5669,f5665])).

fof(f5644,plain,
    ( ~ r1_tarski(sK3,sK1)
    | ~ r1_tarski(sK1,sK3)
    | spl34_4 ),
    inference(extensionality_resolution,[],[f694,f995])).

fof(f5663,plain,
    ( ~ spl34_101
    | ~ spl34_102
    | spl34_4 ),
    inference(avatar_split_clause,[],[f5643,f993,f5660,f5656])).

fof(f5643,plain,
    ( ~ r2_hidden(sK19(sK3,sK1),sK1)
    | ~ r2_hidden(sK19(sK3,sK1),sK3)
    | spl34_4 ),
    inference(extensionality_resolution,[],[f696,f995])).

fof(f696,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK19(X0,X1),X1)
      | ~ r2_hidden(sK19(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f477])).

fof(f5654,plain,
    ( ~ spl34_99
    | ~ spl34_100
    | spl34_4 ),
    inference(avatar_split_clause,[],[f5642,f993,f5651,f5647])).

fof(f5642,plain,
    ( ~ r2_hidden(sK19(sK1,sK3),sK3)
    | ~ r2_hidden(sK19(sK1,sK3),sK1)
    | spl34_4 ),
    inference(extensionality_resolution,[],[f696,f995])).

fof(f5641,plain,
    ( spl34_98
    | ~ spl34_5
    | ~ spl34_91 ),
    inference(avatar_split_clause,[],[f5601,f5024,f997,f5638])).

fof(f5024,plain,
    ( spl34_91
  <=> sP31(sK7(k1_xboole_0),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_91])])).

fof(f5601,plain,
    ( sP31(sK7(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl34_5
    | ~ spl34_91 ),
    inference(backward_demodulation,[],[f5026,f998])).

fof(f5026,plain,
    ( sP31(sK7(k1_xboole_0),k1_xboole_0,sK2)
    | ~ spl34_91 ),
    inference(avatar_component_clause,[],[f5024])).

fof(f5636,plain,
    ( ~ spl34_97
    | ~ spl34_5
    | spl34_90 ),
    inference(avatar_split_clause,[],[f5600,f4987,f997,f5633])).

fof(f5633,plain,
    ( spl34_97
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_97])])).

fof(f4987,plain,
    ( spl34_90
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_90])])).

fof(f5600,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_xboole_0)
    | ~ spl34_5
    | spl34_90 ),
    inference(backward_demodulation,[],[f4989,f998])).

fof(f4989,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k1_xboole_0)
    | spl34_90 ),
    inference(avatar_component_clause,[],[f4987])).

fof(f5625,plain,
    ( ~ spl34_86
    | ~ spl34_5
    | spl34_76 ),
    inference(avatar_split_clause,[],[f5583,f4014,f997,f4874])).

fof(f4874,plain,
    ( spl34_86
  <=> r2_hidden(sK19(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_86])])).

fof(f4014,plain,
    ( spl34_76
  <=> r2_hidden(sK19(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_76])])).

fof(f5583,plain,
    ( ~ r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | spl34_76 ),
    inference(backward_demodulation,[],[f4016,f998])).

fof(f4016,plain,
    ( ~ r2_hidden(sK19(sK2,sK0),sK0)
    | spl34_76 ),
    inference(avatar_component_clause,[],[f4014])).

fof(f5624,plain,
    ( ~ spl34_86
    | ~ spl34_5
    | spl34_75 ),
    inference(avatar_split_clause,[],[f5582,f4010,f997,f4874])).

fof(f4010,plain,
    ( spl34_75
  <=> r2_hidden(sK19(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_75])])).

fof(f5582,plain,
    ( ~ r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | spl34_75 ),
    inference(backward_demodulation,[],[f4012,f998])).

fof(f4012,plain,
    ( ~ r2_hidden(sK19(sK2,sK0),sK2)
    | spl34_75 ),
    inference(avatar_component_clause,[],[f4010])).

fof(f5623,plain,
    ( ~ spl34_86
    | ~ spl34_5
    | spl34_74 ),
    inference(avatar_split_clause,[],[f5581,f4005,f997,f4874])).

fof(f4005,plain,
    ( spl34_74
  <=> r2_hidden(sK19(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_74])])).

fof(f5581,plain,
    ( ~ r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | spl34_74 ),
    inference(backward_demodulation,[],[f4007,f998])).

fof(f4007,plain,
    ( ~ r2_hidden(sK19(sK0,sK2),sK2)
    | spl34_74 ),
    inference(avatar_component_clause,[],[f4005])).

fof(f5622,plain,
    ( ~ spl34_86
    | ~ spl34_5
    | spl34_73 ),
    inference(avatar_split_clause,[],[f5580,f4001,f997,f4874])).

fof(f4001,plain,
    ( spl34_73
  <=> r2_hidden(sK19(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_73])])).

fof(f5580,plain,
    ( ~ r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | spl34_73 ),
    inference(backward_demodulation,[],[f4003,f998])).

fof(f4003,plain,
    ( ~ r2_hidden(sK19(sK0,sK2),sK0)
    | spl34_73 ),
    inference(avatar_component_clause,[],[f4001])).

fof(f5621,plain,
    ( ~ spl34_96
    | ~ spl34_5
    | spl34_60 ),
    inference(avatar_split_clause,[],[f5576,f3473,f997,f5618])).

fof(f5618,plain,
    ( spl34_96
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_96])])).

fof(f3473,plain,
    ( spl34_60
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_60])])).

fof(f5576,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl34_5
    | spl34_60 ),
    inference(backward_demodulation,[],[f3475,f998])).

fof(f3475,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | spl34_60 ),
    inference(avatar_component_clause,[],[f3473])).

fof(f5616,plain,
    ( spl34_95
    | ~ spl34_5
    | ~ spl34_59 ),
    inference(avatar_split_clause,[],[f5575,f3467,f997,f5613])).

fof(f5613,plain,
    ( spl34_95
  <=> sP31(sK7(k2_zfmisc_1(sK0,sK1)),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_95])])).

fof(f3467,plain,
    ( spl34_59
  <=> sP31(sK7(k2_zfmisc_1(sK0,sK1)),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_59])])).

fof(f5575,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),k1_xboole_0,sK0)
    | ~ spl34_5
    | ~ spl34_59 ),
    inference(backward_demodulation,[],[f3469,f998])).

fof(f3469,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),k1_xboole_0,sK2)
    | ~ spl34_59 ),
    inference(avatar_component_clause,[],[f3467])).

fof(f5611,plain,
    ( ~ spl34_94
    | ~ spl34_5
    | spl34_57 ),
    inference(avatar_split_clause,[],[f5573,f3457,f997,f5608])).

fof(f5608,plain,
    ( spl34_94
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK0)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_94])])).

fof(f3457,plain,
    ( spl34_57
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_57])])).

fof(f5573,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK0)),k2_zfmisc_1(sK0,sK1))
    | ~ spl34_5
    | spl34_57 ),
    inference(backward_demodulation,[],[f3459,f998])).

fof(f3459,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | spl34_57 ),
    inference(avatar_component_clause,[],[f3457])).

fof(f5606,plain,
    ( ~ spl34_93
    | ~ spl34_5
    | spl34_31 ),
    inference(avatar_split_clause,[],[f5545,f1705,f997,f5603])).

fof(f5603,plain,
    ( spl34_93
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_93])])).

fof(f1705,plain,
    ( spl34_31
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_31])])).

fof(f5545,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3))),k1_xboole_0)
    | ~ spl34_5
    | spl34_31 ),
    inference(backward_demodulation,[],[f1707,f998])).

fof(f1707,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))),k1_xboole_0)
    | spl34_31 ),
    inference(avatar_component_clause,[],[f1705])).

fof(f5534,plain,
    ( spl34_5
    | ~ spl34_19
    | ~ spl34_20 ),
    inference(avatar_split_clause,[],[f5107,f1317,f1313,f997])).

fof(f1313,plain,
    ( spl34_19
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_19])])).

fof(f1317,plain,
    ( spl34_20
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_20])])).

fof(f5107,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl34_20 ),
    inference(resolution,[],[f1318,f694])).

fof(f1318,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl34_20 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f5533,plain,
    ( spl34_2
    | ~ spl34_49 ),
    inference(avatar_split_clause,[],[f5522,f3381,f983])).

fof(f3381,plain,
    ( spl34_49
  <=> ! [X5] : ~ r2_hidden(X5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_49])])).

fof(f5522,plain,
    ( k1_xboole_0 = sK0
    | ~ spl34_49 ),
    inference(resolution,[],[f3382,f578])).

fof(f3382,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK0)
    | ~ spl34_49 ),
    inference(avatar_component_clause,[],[f3381])).

fof(f5532,plain,
    ( spl34_92
    | spl34_2
    | ~ spl34_49 ),
    inference(avatar_split_clause,[],[f5521,f3381,f983,f5529])).

fof(f5521,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK0
        | sK0 = k2_tarski(X1,X1) )
    | ~ spl34_49 ),
    inference(resolution,[],[f3382,f810])).

fof(f5531,plain,
    ( spl34_92
    | spl34_2
    | ~ spl34_49 ),
    inference(avatar_split_clause,[],[f5520,f3381,f983,f5529])).

fof(f5520,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | k2_tarski(X0,X0) = sK0 )
    | ~ spl34_49 ),
    inference(resolution,[],[f3382,f808])).

fof(f5027,plain,
    ( spl34_91
    | ~ spl34_29
    | ~ spl34_59 ),
    inference(avatar_split_clause,[],[f5005,f3467,f1691,f5024])).

fof(f1691,plain,
    ( spl34_29
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_29])])).

fof(f5005,plain,
    ( sP31(sK7(k1_xboole_0),k1_xboole_0,sK2)
    | ~ spl34_29
    | ~ spl34_59 ),
    inference(backward_demodulation,[],[f3469,f1693])).

fof(f1693,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_29 ),
    inference(avatar_component_clause,[],[f1691])).

fof(f5022,plain,
    ( ~ spl34_90
    | ~ spl34_29
    | spl34_57 ),
    inference(avatar_split_clause,[],[f5004,f3457,f1691,f4987])).

fof(f5004,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k1_xboole_0)
    | ~ spl34_29
    | spl34_57 ),
    inference(backward_demodulation,[],[f3459,f1693])).

fof(f4993,plain,
    ( ~ spl34_90
    | spl34_26
    | ~ spl34_29
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4992,f3398,f1691,f1623,f4987])).

fof(f1623,plain,
    ( spl34_26
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_26])])).

fof(f3398,plain,
    ( spl34_53
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_53])])).

fof(f4992,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k1_xboole_0)
    | spl34_26
    | ~ spl34_29
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4991,f587])).

fof(f587,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f4991,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0))),k1_xboole_0)
    | spl34_26
    | ~ spl34_29
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f1701,f3400])).

fof(f3400,plain,
    ( k1_xboole_0 = sK3
    | ~ spl34_53 ),
    inference(avatar_component_clause,[],[f3398])).

fof(f1701,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))),k1_xboole_0)
    | spl34_26
    | ~ spl34_29 ),
    inference(backward_demodulation,[],[f1625,f1693])).

fof(f1625,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK1))
    | spl34_26 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f4990,plain,
    ( ~ spl34_90
    | spl34_31
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4985,f3398,f1705,f4987])).

fof(f4985,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k1_xboole_0)
    | spl34_31
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4984,f587])).

fof(f4984,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0))),k1_xboole_0)
    | spl34_31
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f1707,f3400])).

fof(f4973,plain,
    ( spl34_29
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4972,f3398,f988,f1691])).

fof(f988,plain,
    ( spl34_3
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_3])])).

fof(f4972,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4971,f943])).

fof(f4971,plain,
    ( ! [X4] : k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k4_xboole_0(sK2,X4),k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4970,f588])).

fof(f4970,plain,
    ( ! [X4] : k2_zfmisc_1(k4_xboole_0(sK2,X4),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4939,f943])).

fof(f4939,plain,
    ( ! [X4] : k2_zfmisc_1(k4_xboole_0(sK2,X4),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,k1_xboole_0))
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f4151,f3400])).

fof(f4151,plain,
    ( ! [X4] : k2_zfmisc_1(k4_xboole_0(sK2,X4),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))
    | ~ spl34_3 ),
    inference(superposition,[],[f782,f990])).

fof(f990,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl34_3 ),
    inference(avatar_component_clause,[],[f988])).

fof(f782,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f335])).

fof(f335,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f4967,plain,
    ( spl34_89
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4962,f3398,f988,f4964])).

fof(f4964,plain,
    ( spl34_89
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_89])])).

fof(f4962,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4961,f943])).

fof(f4961,plain,
    ( ! [X4] : k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(X4,sK2),k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4936,f943])).

fof(f4936,plain,
    ( ! [X4] : k2_zfmisc_1(k2_xboole_0(X4,sK2),k1_xboole_0) = k2_xboole_0(k2_zfmisc_1(X4,k1_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f4067,f3400])).

fof(f4067,plain,
    ( ! [X4] : k2_zfmisc_1(k2_xboole_0(X4,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl34_3 ),
    inference(superposition,[],[f780,f990])).

fof(f780,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f330])).

fof(f330,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f4960,plain,
    ( spl34_88
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4955,f3398,f988,f4957])).

fof(f4957,plain,
    ( spl34_88
  <=> k1_xboole_0 = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_88])])).

fof(f4955,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4954,f943])).

fof(f4954,plain,
    ( ! [X4] : k2_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(sK2,X4),k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4935,f943])).

fof(f4935,plain,
    ( ! [X4] : k2_zfmisc_1(k2_xboole_0(sK2,X4),k1_xboole_0) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,k1_xboole_0))
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f4064,f3400])).

fof(f4064,plain,
    ( ! [X4] : k2_zfmisc_1(k2_xboole_0(sK2,X4),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))
    | ~ spl34_3 ),
    inference(superposition,[],[f780,f990])).

fof(f4952,plain,
    ( spl34_61
    | spl34_34
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4951,f3398,f988,f1724,f3479])).

fof(f3479,plain,
    ( spl34_61
  <=> ! [X4] : ~ r1_tarski(sK2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_61])])).

fof(f1724,plain,
    ( spl34_34
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_34])])).

fof(f4951,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
        | ~ r1_tarski(sK2,X4) )
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4913,f943])).

fof(f4913,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,k1_xboole_0))
        | ~ r1_tarski(sK2,X4) )
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1852,f3400])).

fof(f1852,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))
        | ~ r1_tarski(sK2,X4) )
    | ~ spl34_3 ),
    inference(superposition,[],[f774,f990])).

fof(f774,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f506])).

fof(f506,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f328])).

fof(f328,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f4947,plain,
    ( spl34_29
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f4946,f3398,f988,f1691])).

fof(f4946,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f4900,f943])).

fof(f4900,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f990,f3400])).

fof(f4899,plain,
    ( spl34_29
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3447,f3398,f988,f1691])).

fof(f3447,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f3420,f943])).

fof(f3420,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0)
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f990,f3400])).

fof(f4898,plain,
    ( ~ spl34_78
    | spl34_52
    | ~ spl34_50 ),
    inference(avatar_split_clause,[],[f4695,f3384,f3391,f4058])).

fof(f4058,plain,
    ( spl34_78
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_78])])).

fof(f3391,plain,
    ( spl34_52
  <=> ! [X6] : ~ r2_hidden(X6,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_52])])).

fof(f4695,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(sK3) )
    | ~ spl34_50 ),
    inference(resolution,[],[f3385,f1151])).

fof(f1151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f1147,f582])).

fof(f582,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f453])).

fof(f453,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f4897,plain,
    ( spl34_53
    | spl34_55
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3485,f988,f3417,f3398])).

fof(f3417,plain,
    ( spl34_55
  <=> ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_55])])).

fof(f3485,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | k1_xboole_0 = sK3
        | r1_tarski(X1,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f520,f990])).

fof(f520,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f433])).

fof(f433,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f327])).

fof(f327,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f4896,plain,
    ( spl34_53
    | spl34_55
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3618,f988,f3417,f3398])).

fof(f3618,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | k1_xboole_0 = sK3
        | r1_tarski(X1,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f520,f990])).

fof(f4895,plain,
    ( spl34_53
    | spl34_54
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3484,f988,f3413,f3398])).

fof(f3413,plain,
    ( spl34_54
  <=> ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))
        | r1_tarski(sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_54])])).

fof(f3484,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | k1_xboole_0 = sK3
        | r1_tarski(sK2,X0) )
    | ~ spl34_3 ),
    inference(superposition,[],[f520,f990])).

fof(f4894,plain,
    ( spl34_53
    | spl34_54
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3617,f988,f3413,f3398])).

fof(f3617,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | k1_xboole_0 = sK3
        | r1_tarski(sK2,X0) )
    | ~ spl34_3 ),
    inference(superposition,[],[f520,f990])).

fof(f4893,plain,
    ( ~ spl34_35
    | spl34_87
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f1945,f988,f4891,f1741])).

fof(f1741,plain,
    ( spl34_35
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_35])])).

fof(f4891,plain,
    ( spl34_87
  <=> ! [X2] : ~ sP31(X2,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_87])])).

fof(f1945,plain,
    ( ! [X2] :
        ( ~ sP31(X2,sK3,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl34_3 ),
    inference(resolution,[],[f1643,f1151])).

fof(f1643,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ sP31(X0,sK3,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f975,f990])).

fof(f4889,plain,
    ( spl34_62
    | spl34_53
    | ~ spl34_29
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f2218,f988,f1691,f3398,f3517])).

fof(f3517,plain,
    ( spl34_62
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_62])])).

fof(f2218,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl34_3 ),
    inference(superposition,[],[f556,f990])).

fof(f556,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f323])).

fof(f4888,plain,
    ( spl34_62
    | spl34_53
    | ~ spl34_29
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3486,f988,f1691,f3398,f3517])).

fof(f3486,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl34_3 ),
    inference(superposition,[],[f556,f990])).

fof(f4887,plain,
    ( spl34_62
    | spl34_53
    | ~ spl34_29
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3621,f988,f1691,f3398,f3517])).

fof(f3621,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl34_3 ),
    inference(superposition,[],[f556,f990])).

fof(f4880,plain,
    ( spl34_86
    | ~ spl34_5
    | ~ spl34_76 ),
    inference(avatar_split_clause,[],[f4818,f4014,f997,f4874])).

fof(f4818,plain,
    ( r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | ~ spl34_76 ),
    inference(backward_demodulation,[],[f4015,f998])).

fof(f4015,plain,
    ( r2_hidden(sK19(sK2,sK0),sK0)
    | ~ spl34_76 ),
    inference(avatar_component_clause,[],[f4014])).

fof(f4879,plain,
    ( spl34_86
    | ~ spl34_5
    | ~ spl34_75 ),
    inference(avatar_split_clause,[],[f4817,f4010,f997,f4874])).

fof(f4817,plain,
    ( r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | ~ spl34_75 ),
    inference(backward_demodulation,[],[f4011,f998])).

fof(f4011,plain,
    ( r2_hidden(sK19(sK2,sK0),sK2)
    | ~ spl34_75 ),
    inference(avatar_component_clause,[],[f4010])).

fof(f4878,plain,
    ( spl34_86
    | ~ spl34_5
    | ~ spl34_74 ),
    inference(avatar_split_clause,[],[f4816,f4005,f997,f4874])).

fof(f4816,plain,
    ( r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | ~ spl34_74 ),
    inference(backward_demodulation,[],[f4006,f998])).

fof(f4006,plain,
    ( r2_hidden(sK19(sK0,sK2),sK2)
    | ~ spl34_74 ),
    inference(avatar_component_clause,[],[f4005])).

fof(f4877,plain,
    ( spl34_86
    | ~ spl34_5
    | ~ spl34_73 ),
    inference(avatar_split_clause,[],[f4815,f4001,f997,f4874])).

fof(f4815,plain,
    ( r2_hidden(sK19(sK0,sK0),sK0)
    | ~ spl34_5
    | ~ spl34_73 ),
    inference(backward_demodulation,[],[f4002,f998])).

fof(f4002,plain,
    ( r2_hidden(sK19(sK0,sK2),sK0)
    | ~ spl34_73 ),
    inference(avatar_component_clause,[],[f4001])).

fof(f4872,plain,
    ( ~ spl34_85
    | ~ spl34_5
    | spl34_44 ),
    inference(avatar_split_clause,[],[f4800,f2224,f997,f4867])).

fof(f4867,plain,
    ( spl34_85
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_85])])).

fof(f2224,plain,
    ( spl34_44
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_44])])).

fof(f4800,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | ~ spl34_5
    | spl34_44 ),
    inference(backward_demodulation,[],[f2226,f998])).

fof(f2226,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl34_44 ),
    inference(avatar_component_clause,[],[f2224])).

fof(f4871,plain,
    ( ~ spl34_85
    | ~ spl34_5
    | spl34_42 ),
    inference(avatar_split_clause,[],[f4799,f2135,f997,f4867])).

fof(f2135,plain,
    ( spl34_42
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_42])])).

fof(f4799,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | ~ spl34_5
    | spl34_42 ),
    inference(backward_demodulation,[],[f2137,f998])).

fof(f2137,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl34_42 ),
    inference(avatar_component_clause,[],[f2135])).

fof(f4870,plain,
    ( ~ spl34_85
    | ~ spl34_5
    | spl34_41 ),
    inference(avatar_split_clause,[],[f4798,f2130,f997,f4867])).

fof(f2130,plain,
    ( spl34_41
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_41])])).

fof(f4798,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | ~ spl34_5
    | spl34_41 ),
    inference(backward_demodulation,[],[f2132,f998])).

fof(f2132,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl34_41 ),
    inference(avatar_component_clause,[],[f2130])).

fof(f4865,plain,
    ( ~ spl34_84
    | ~ spl34_5
    | spl34_39 ),
    inference(avatar_split_clause,[],[f4787,f1844,f997,f4862])).

fof(f4862,plain,
    ( spl34_84
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_84])])).

fof(f1844,plain,
    ( spl34_39
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_39])])).

fof(f4787,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3))))
    | ~ spl34_5
    | spl34_39 ),
    inference(backward_demodulation,[],[f1846,f998])).

fof(f1846,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))
    | spl34_39 ),
    inference(avatar_component_clause,[],[f1844])).

fof(f4860,plain,
    ( spl34_83
    | ~ spl34_5
    | ~ spl34_30 ),
    inference(avatar_split_clause,[],[f4783,f1695,f997,f4857])).

fof(f4857,plain,
    ( spl34_83
  <=> sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_83])])).

fof(f1695,plain,
    ( spl34_30
  <=> sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_30])])).

fof(f4783,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,sK0)
    | ~ spl34_5
    | ~ spl34_30 ),
    inference(backward_demodulation,[],[f1697,f998])).

fof(f1697,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,sK2)
    | ~ spl34_30 ),
    inference(avatar_component_clause,[],[f1695])).

fof(f4855,plain,
    ( ~ spl34_82
    | ~ spl34_5
    | spl34_27 ),
    inference(avatar_split_clause,[],[f4779,f1628,f997,f4852])).

fof(f4852,plain,
    ( spl34_82
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_82])])).

fof(f1628,plain,
    ( spl34_27
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_27])])).

fof(f4779,plain,
    ( ~ r1_tarski(sK0,sK3)
    | ~ spl34_5
    | spl34_27 ),
    inference(backward_demodulation,[],[f1630,f998])).

fof(f1630,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl34_27 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f4850,plain,
    ( ~ spl34_81
    | ~ spl34_5
    | spl34_26 ),
    inference(avatar_split_clause,[],[f4778,f1623,f997,f4847])).

fof(f4847,plain,
    ( spl34_81
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_81])])).

fof(f4778,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3))),k2_zfmisc_1(sK0,sK1))
    | ~ spl34_5
    | spl34_26 ),
    inference(backward_demodulation,[],[f1625,f998])).

fof(f4845,plain,
    ( spl34_80
    | ~ spl34_5
    | ~ spl34_23 ),
    inference(avatar_split_clause,[],[f4776,f1406,f997,f4842])).

fof(f4842,plain,
    ( spl34_80
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_80])])).

fof(f1406,plain,
    ( spl34_23
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_23])])).

fof(f4776,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK3))))
    | ~ spl34_5
    | ~ spl34_23 ),
    inference(backward_demodulation,[],[f1408,f998])).

fof(f1408,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))
    | ~ spl34_23 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f4840,plain,
    ( spl34_79
    | ~ spl34_3
    | ~ spl34_5 ),
    inference(avatar_split_clause,[],[f4774,f997,f988,f4837])).

fof(f4837,plain,
    ( spl34_79
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_79])])).

fof(f4774,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl34_3
    | ~ spl34_5 ),
    inference(backward_demodulation,[],[f990,f998])).

fof(f4773,plain,
    ( spl34_5
    | ~ spl34_75
    | ~ spl34_76 ),
    inference(avatar_split_clause,[],[f4333,f4014,f4010,f997])).

fof(f4333,plain,
    ( ~ r2_hidden(sK19(sK2,sK0),sK2)
    | sK0 = sK2
    | ~ spl34_76 ),
    inference(resolution,[],[f4015,f696])).

fof(f4772,plain,
    ( spl34_5
    | ~ spl34_19
    | ~ spl34_20 ),
    inference(avatar_split_clause,[],[f3635,f1317,f1313,f997])).

fof(f3635,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl34_20 ),
    inference(resolution,[],[f1318,f694])).

fof(f4771,plain,
    ( ~ spl34_73
    | ~ spl34_51
    | spl34_74 ),
    inference(avatar_split_clause,[],[f4768,f4005,f3388,f4001])).

fof(f3388,plain,
    ( spl34_51
  <=> ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_51])])).

fof(f4768,plain,
    ( ~ r2_hidden(sK19(sK0,sK2),sK0)
    | ~ spl34_51
    | spl34_74 ),
    inference(resolution,[],[f3389,f4007])).

fof(f3389,plain,
    ( ! [X7] :
        ( r2_hidden(X7,sK2)
        | ~ r2_hidden(X7,sK0) )
    | ~ spl34_51 ),
    inference(avatar_component_clause,[],[f3388])).

fof(f4770,plain,
    ( ~ spl34_76
    | ~ spl34_51
    | spl34_75 ),
    inference(avatar_split_clause,[],[f4767,f4010,f3388,f4014])).

fof(f4767,plain,
    ( ~ r2_hidden(sK19(sK2,sK0),sK0)
    | ~ spl34_51
    | spl34_75 ),
    inference(resolution,[],[f3389,f4012])).

fof(f4650,plain,
    ( spl34_5
    | spl34_73
    | spl34_74 ),
    inference(avatar_split_clause,[],[f4649,f4005,f4001,f997])).

fof(f4649,plain,
    ( r2_hidden(sK19(sK0,sK2),sK0)
    | sK0 = sK2
    | spl34_74 ),
    inference(resolution,[],[f4007,f695])).

fof(f4638,plain,
    ( ~ spl34_74
    | ~ spl34_45
    | spl34_73 ),
    inference(avatar_split_clause,[],[f4636,f4001,f3367,f4005])).

fof(f3367,plain,
    ( spl34_45
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_45])])).

fof(f4636,plain,
    ( ~ r2_hidden(sK19(sK0,sK2),sK2)
    | ~ spl34_45
    | spl34_73 ),
    inference(resolution,[],[f3368,f4003])).

fof(f3368,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl34_45 ),
    inference(avatar_component_clause,[],[f3367])).

fof(f4201,plain,
    ( spl34_5
    | spl34_75
    | spl34_76 ),
    inference(avatar_split_clause,[],[f4200,f4014,f4010,f997])).

fof(f4200,plain,
    ( r2_hidden(sK19(sK2,sK0),sK2)
    | sK0 = sK2
    | spl34_76 ),
    inference(resolution,[],[f4016,f695])).

fof(f4061,plain,
    ( ~ spl34_78
    | spl34_77 ),
    inference(avatar_split_clause,[],[f4055,f4023,f4058])).

fof(f4023,plain,
    ( spl34_77
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_77])])).

fof(f4055,plain,
    ( ~ v1_xboole_0(sK3)
    | spl34_77 ),
    inference(resolution,[],[f4025,f1053])).

fof(f1053,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f593,f582])).

fof(f593,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f4025,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl34_77 ),
    inference(avatar_component_clause,[],[f4023])).

fof(f4043,plain,(
    spl34_66 ),
    inference(avatar_contradiction_clause,[],[f4040])).

fof(f4040,plain,
    ( $false
    | spl34_66 ),
    inference(resolution,[],[f3582,f593])).

fof(f3582,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl34_66 ),
    inference(avatar_component_clause,[],[f3580])).

fof(f3580,plain,
    ( spl34_66
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_66])])).

fof(f4027,plain,
    ( ~ spl34_77
    | ~ spl34_66
    | spl34_53 ),
    inference(avatar_split_clause,[],[f4021,f3398,f3580,f4023])).

fof(f4021,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | spl34_53 ),
    inference(extensionality_resolution,[],[f694,f3399])).

fof(f3399,plain,
    ( k1_xboole_0 != sK3
    | spl34_53 ),
    inference(avatar_component_clause,[],[f3398])).

fof(f4026,plain,
    ( ~ spl34_66
    | ~ spl34_77
    | spl34_53 ),
    inference(avatar_split_clause,[],[f4020,f3398,f4023,f3580])).

fof(f4020,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | spl34_53 ),
    inference(extensionality_resolution,[],[f694,f3399])).

fof(f4017,plain,
    ( ~ spl34_75
    | ~ spl34_76
    | spl34_5 ),
    inference(avatar_split_clause,[],[f3992,f997,f4014,f4010])).

fof(f3992,plain,
    ( ~ r2_hidden(sK19(sK2,sK0),sK0)
    | ~ r2_hidden(sK19(sK2,sK0),sK2)
    | spl34_5 ),
    inference(extensionality_resolution,[],[f696,f999])).

fof(f999,plain,
    ( sK0 != sK2
    | spl34_5 ),
    inference(avatar_component_clause,[],[f997])).

fof(f4008,plain,
    ( ~ spl34_73
    | ~ spl34_74
    | spl34_5 ),
    inference(avatar_split_clause,[],[f3991,f997,f4005,f4001])).

fof(f3991,plain,
    ( ~ r2_hidden(sK19(sK0,sK2),sK2)
    | ~ r2_hidden(sK19(sK0,sK2),sK0)
    | spl34_5 ),
    inference(extensionality_resolution,[],[f696,f999])).

fof(f3724,plain,
    ( ~ spl34_58
    | ~ spl34_72
    | spl34_62 ),
    inference(avatar_split_clause,[],[f3718,f3517,f3720,f3462])).

fof(f3462,plain,
    ( spl34_58
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_58])])).

fof(f3720,plain,
    ( spl34_72
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_72])])).

fof(f3718,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(sK2,k1_xboole_0)
    | spl34_62 ),
    inference(extensionality_resolution,[],[f694,f3518])).

fof(f3518,plain,
    ( k1_xboole_0 != sK2
    | spl34_62 ),
    inference(avatar_component_clause,[],[f3517])).

fof(f3723,plain,
    ( ~ spl34_72
    | ~ spl34_58
    | spl34_62 ),
    inference(avatar_split_clause,[],[f3717,f3517,f3462,f3720])).

fof(f3717,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | spl34_62 ),
    inference(extensionality_resolution,[],[f694,f3518])).

fof(f3613,plain,
    ( ~ spl34_24
    | spl34_42 ),
    inference(avatar_split_clause,[],[f2213,f2135,f1414])).

fof(f1414,plain,
    ( spl34_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_24])])).

fof(f2213,plain,
    ( ~ v1_xboole_0(sK2)
    | spl34_42 ),
    inference(resolution,[],[f2137,f1052])).

fof(f1052,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f594,f582])).

fof(f594,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f3610,plain,
    ( ~ spl34_71
    | spl34_44
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3558,f3517,f2224,f3607])).

fof(f3607,plain,
    ( spl34_71
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_71])])).

fof(f3558,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl34_44
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f2226,f3519])).

fof(f3519,plain,
    ( k1_xboole_0 = sK2
    | ~ spl34_62 ),
    inference(avatar_component_clause,[],[f3517])).

fof(f3605,plain,
    ( ~ spl34_70
    | spl34_41
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3557,f3517,f2130,f3602])).

fof(f3602,plain,
    ( spl34_70
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_70])])).

fof(f3557,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl34_41
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f2132,f3519])).

fof(f3599,plain,
    ( spl34_69
    | spl34_34
    | ~ spl34_3
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3595,f3517,f988,f1724,f3597])).

fof(f3597,plain,
    ( spl34_69
  <=> ! [X4] : ~ r1_tarski(sK3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_69])])).

fof(f3595,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
        | ~ r1_tarski(sK3,X4) )
    | ~ spl34_3
    | ~ spl34_62 ),
    inference(forward_demodulation,[],[f3549,f944])).

fof(f944,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f557])).

fof(f557,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f323])).

fof(f3549,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_xboole_0,X4))
        | ~ r1_tarski(sK3,X4) )
    | ~ spl34_3
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f1862,f3519])).

fof(f1862,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X4))
        | ~ r1_tarski(sK3,X4) )
    | ~ spl34_3 ),
    inference(superposition,[],[f775,f990])).

fof(f775,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f506])).

fof(f3594,plain,
    ( ~ spl34_68
    | spl34_39
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3589,f3517,f1844,f3591])).

fof(f3591,plain,
    ( spl34_68
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_68])])).

fof(f3589,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | spl34_39
    | ~ spl34_62 ),
    inference(forward_demodulation,[],[f3546,f1096])).

fof(f1096,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f724,f587])).

fof(f724,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3546,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK3))))
    | spl34_39
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f1846,f3519])).

fof(f3588,plain,
    ( spl34_67
    | ~ spl34_30
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3542,f3517,f1695,f3585])).

fof(f3585,plain,
    ( spl34_67
  <=> sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_67])])).

fof(f3542,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,k1_xboole_0)
    | ~ spl34_30
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f1697,f3519])).

fof(f3583,plain,
    ( ~ spl34_66
    | spl34_27
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3538,f3517,f1628,f3580])).

fof(f3538,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl34_27
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f1630,f3519])).

fof(f3578,plain,
    ( ~ spl34_65
    | spl34_26
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3573,f3517,f1623,f3575])).

fof(f3575,plain,
    ( spl34_65
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_65])])).

fof(f3573,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK3)),k2_zfmisc_1(sK0,sK1))
    | spl34_26
    | ~ spl34_62 ),
    inference(forward_demodulation,[],[f3537,f1096])).

fof(f3537,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK3))),k2_zfmisc_1(sK0,sK1))
    | spl34_26
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f1625,f3519])).

fof(f3572,plain,
    ( spl34_28
    | ~ spl34_23
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3571,f3517,f1406,f1632])).

fof(f1632,plain,
    ( spl34_28
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_28])])).

fof(f3571,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl34_23
    | ~ spl34_62 ),
    inference(forward_demodulation,[],[f3536,f1096])).

fof(f3536,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK3))))
    | ~ spl34_23
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f1408,f3519])).

fof(f3570,plain,
    ( spl34_29
    | ~ spl34_3
    | ~ spl34_62 ),
    inference(avatar_split_clause,[],[f3569,f3517,f988,f1691])).

fof(f3569,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3
    | ~ spl34_62 ),
    inference(forward_demodulation,[],[f3534,f944])).

fof(f3534,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl34_3
    | ~ spl34_62 ),
    inference(backward_demodulation,[],[f990,f3519])).

fof(f3533,plain,
    ( ~ spl34_42
    | spl34_43
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f2222,f988,f2139,f2135])).

fof(f2139,plain,
    ( spl34_43
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_43])])).

fof(f2222,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ r1_xboole_0(sK2,sK2)
    | ~ spl34_3 ),
    inference(superposition,[],[f1807,f990])).

fof(f1807,plain,
    ( ! [X6,X7] :
        ( r1_xboole_0(k2_zfmisc_1(X6,X7),k2_zfmisc_1(sK0,sK1))
        | ~ r1_xboole_0(X6,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f755,f990])).

fof(f755,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f498])).

fof(f498,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f337])).

fof(f337,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f3532,plain,
    ( ~ spl34_42
    | spl34_43
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3500,f988,f2139,f2135])).

fof(f3500,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ r1_xboole_0(sK2,sK2)
    | ~ spl34_3 ),
    inference(superposition,[],[f1804,f990])).

fof(f1804,plain,
    ( ! [X6,X7] :
        ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,X7))
        | ~ r1_xboole_0(sK2,X6) )
    | ~ spl34_3 ),
    inference(superposition,[],[f755,f990])).

fof(f3531,plain,
    ( ~ spl34_42
    | spl34_43
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3501,f988,f2139,f2135])).

fof(f3501,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ r1_xboole_0(sK2,sK2)
    | ~ spl34_3 ),
    inference(superposition,[],[f1807,f990])).

fof(f3530,plain,
    ( ~ spl34_24
    | spl34_27 ),
    inference(avatar_split_clause,[],[f1640,f1628,f1414])).

fof(f1640,plain,
    ( ~ v1_xboole_0(sK2)
    | spl34_27 ),
    inference(resolution,[],[f1630,f1053])).

fof(f3529,plain,
    ( ~ spl34_24
    | spl34_44 ),
    inference(avatar_split_clause,[],[f2280,f2224,f1414])).

fof(f2280,plain,
    ( ~ v1_xboole_0(sK2)
    | spl34_44 ),
    inference(resolution,[],[f2226,f1052])).

fof(f3528,plain,
    ( ~ spl34_24
    | spl34_27 ),
    inference(avatar_split_clause,[],[f3483,f1628,f1414])).

fof(f3483,plain,
    ( ~ v1_xboole_0(sK2)
    | spl34_27 ),
    inference(resolution,[],[f1630,f1053])).

fof(f3527,plain,
    ( spl34_62
    | spl34_64
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3515,f988,f3525,f3517])).

fof(f3525,plain,
    ( spl34_64
  <=> ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,X4),k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_64])])).

fof(f3515,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,X4),k2_zfmisc_1(sK0,sK1))
        | k1_xboole_0 = sK2
        | r1_tarski(X4,sK3) )
    | ~ spl34_3 ),
    inference(superposition,[],[f521,f990])).

fof(f521,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f433])).

fof(f3523,plain,
    ( spl34_62
    | spl34_63
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3512,f988,f3521,f3517])).

fof(f3521,plain,
    ( spl34_63
  <=> ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X4))
        | r1_tarski(sK3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_63])])).

fof(f3512,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X4))
        | k1_xboole_0 = sK2
        | r1_tarski(sK3,X4) )
    | ~ spl34_3 ),
    inference(superposition,[],[f521,f990])).

fof(f3505,plain,
    ( spl34_1
    | ~ spl34_52 ),
    inference(avatar_split_clause,[],[f3502,f3391,f978])).

fof(f978,plain,
    ( spl34_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_1])])).

fof(f3502,plain,
    ( k1_xboole_0 = sK1
    | ~ spl34_52 ),
    inference(resolution,[],[f3392,f578])).

fof(f3392,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK1)
    | ~ spl34_52 ),
    inference(avatar_component_clause,[],[f3391])).

fof(f3481,plain,
    ( spl34_61
    | spl34_34
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3477,f3398,f988,f1724,f3479])).

fof(f3477,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
        | ~ r1_tarski(sK2,X4) )
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f3432,f943])).

fof(f3432,plain,
    ( ! [X4] :
        ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,k1_xboole_0))
        | ~ r1_tarski(sK2,X4) )
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1852,f3400])).

fof(f3476,plain,
    ( ~ spl34_60
    | spl34_39
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3471,f3398,f1844,f3473])).

fof(f3471,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | spl34_39
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f3431,f587])).

fof(f3431,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0))))
    | spl34_39
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1846,f3400])).

fof(f3470,plain,
    ( spl34_59
    | ~ spl34_30
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3427,f3398,f1695,f3467])).

fof(f3427,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),k1_xboole_0,sK2)
    | ~ spl34_30
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1697,f3400])).

fof(f3465,plain,
    ( ~ spl34_58
    | spl34_27
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3423,f3398,f1628,f3462])).

fof(f3423,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl34_27
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1630,f3400])).

fof(f3460,plain,
    ( ~ spl34_57
    | spl34_26
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3455,f3398,f1623,f3457])).

fof(f3455,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | spl34_26
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f3422,f587])).

fof(f3422,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0))),k2_zfmisc_1(sK0,sK1))
    | spl34_26
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1625,f3400])).

fof(f3454,plain,
    ( spl34_56
    | ~ spl34_23
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3449,f3398,f1406,f3451])).

fof(f3451,plain,
    ( spl34_56
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_56])])).

fof(f3449,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ spl34_23
    | ~ spl34_53 ),
    inference(forward_demodulation,[],[f3421,f587])).

fof(f3421,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0))))
    | ~ spl34_23
    | ~ spl34_53 ),
    inference(backward_demodulation,[],[f1408,f3400])).

fof(f3448,plain,
    ( spl34_29
    | ~ spl34_3
    | ~ spl34_53 ),
    inference(avatar_split_clause,[],[f3447,f3398,f988,f1691])).

fof(f3419,plain,
    ( spl34_53
    | spl34_55
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3411,f988,f3417,f3398])).

fof(f3411,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(sK0,sK1))
        | k1_xboole_0 = sK3
        | r1_tarski(X4,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f520,f990])).

fof(f3415,plain,
    ( spl34_53
    | spl34_54
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3408,f988,f3413,f3398])).

fof(f3408,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))
        | k1_xboole_0 = sK3
        | r1_tarski(sK2,X4) )
    | ~ spl34_3 ),
    inference(superposition,[],[f520,f990])).

fof(f3401,plain,
    ( spl34_53
    | ~ spl34_46 ),
    inference(avatar_split_clause,[],[f3394,f3370,f3398])).

fof(f3370,plain,
    ( spl34_46
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_46])])).

fof(f3394,plain,
    ( k1_xboole_0 = sK3
    | ~ spl34_46 ),
    inference(resolution,[],[f3371,f578])).

fof(f3371,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl34_46 ),
    inference(avatar_component_clause,[],[f3370])).

fof(f3393,plain,
    ( spl34_51
    | spl34_52
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3362,f988,f3391,f3388])).

fof(f3362,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK2) )
    | ~ spl34_3 ),
    inference(resolution,[],[f976,f2048])).

fof(f2048,plain,
    ( ! [X2,X3] :
        ( ~ sP31(k4_tarski(X2,X3),sK1,sK0)
        | r2_hidden(X2,sK2) )
    | ~ spl34_3 ),
    inference(resolution,[],[f1783,f975])).

fof(f1783,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X6,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f747,f990])).

fof(f747,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f976,plain,(
    ! [X4,X0,X5,X1] :
      ( sP31(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f766])).

fof(f766,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP31(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f285])).

fof(f3386,plain,
    ( spl34_49
    | spl34_50
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3361,f988,f3384,f3381])).

fof(f3361,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK0)
        | r2_hidden(X4,sK3) )
    | ~ spl34_3 ),
    inference(resolution,[],[f976,f2073])).

fof(f2073,plain,
    ( ! [X2,X3] :
        ( ~ sP31(k4_tarski(X3,X2),sK1,sK0)
        | r2_hidden(X2,sK3) )
    | ~ spl34_3 ),
    inference(resolution,[],[f1795,f975])).

fof(f1795,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X7,sK3) )
    | ~ spl34_3 ),
    inference(superposition,[],[f748,f990])).

fof(f748,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f313])).

fof(f3379,plain,
    ( spl34_47
    | spl34_48
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3360,f988,f3377,f3374])).

fof(f3360,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK3)
        | ~ r2_hidden(X3,sK2)
        | r2_hidden(X2,sK1) )
    | ~ spl34_3 ),
    inference(resolution,[],[f976,f1946])).

fof(f1946,plain,
    ( ! [X4,X3] :
        ( ~ sP31(k4_tarski(X3,X4),sK3,sK2)
        | r2_hidden(X4,sK1) )
    | ~ spl34_3 ),
    inference(resolution,[],[f1643,f748])).

fof(f3372,plain,
    ( spl34_45
    | spl34_46
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f3359,f988,f3370,f3367])).

fof(f3359,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK0) )
    | ~ spl34_3 ),
    inference(resolution,[],[f976,f1947])).

fof(f1947,plain,
    ( ! [X6,X5] :
        ( ~ sP31(k4_tarski(X5,X6),sK3,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl34_3 ),
    inference(resolution,[],[f1643,f747])).

fof(f2227,plain,
    ( spl34_29
    | ~ spl34_44
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f2219,f988,f2224,f1691])).

fof(f2219,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3 ),
    inference(resolution,[],[f1807,f584])).

fof(f584,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f455])).

fof(f455,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f2142,plain,
    ( ~ spl34_42
    | spl34_43
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f2128,f988,f2139,f2135])).

fof(f2128,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ r1_xboole_0(sK2,sK2)
    | ~ spl34_3 ),
    inference(superposition,[],[f1804,f990])).

fof(f2133,plain,
    ( spl34_29
    | ~ spl34_41
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f2125,f988,f2130,f1691])).

fof(f2125,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3 ),
    inference(resolution,[],[f1804,f584])).

fof(f2015,plain,
    ( spl34_40
    | ~ spl34_7 ),
    inference(avatar_split_clause,[],[f1994,f1008,f2012])).

fof(f2012,plain,
    ( spl34_40
  <=> k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = k2_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_40])])).

fof(f1008,plain,
    ( spl34_7
  <=> k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_7])])).

fof(f1994,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = k2_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl34_7 ),
    inference(superposition,[],[f830,f1010])).

fof(f1010,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl34_7 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f830,plain,(
    ! [X0] : k1_zfmisc_1(k2_tarski(X0,X0)) = k2_tarski(k1_xboole_0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f586,f729,f729])).

fof(f586,plain,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f364])).

fof(f364,axiom,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_zfmisc_1)).

fof(f1847,plain,
    ( ~ spl34_39
    | ~ spl34_23
    | spl34_34 ),
    inference(avatar_split_clause,[],[f1840,f1724,f1406,f1844])).

fof(f1840,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))
    | ~ spl34_23
    | spl34_34 ),
    inference(resolution,[],[f1408,f1739])).

fof(f1739,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X0)
        | ~ v1_xboole_0(X0) )
    | spl34_34 ),
    inference(superposition,[],[f1726,f582])).

fof(f1726,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | spl34_34 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f1817,plain,
    ( ~ spl34_37
    | ~ spl34_38
    | spl34_36 ),
    inference(avatar_split_clause,[],[f1808,f1776,f1814,f1810])).

fof(f1810,plain,
    ( spl34_37
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_37])])).

fof(f1814,plain,
    ( spl34_38
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_38])])).

fof(f1776,plain,
    ( spl34_36
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_36])])).

fof(f1808,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ r1_tarski(sK0,sK1)
    | spl34_36 ),
    inference(superposition,[],[f1778,f705])).

fof(f705,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f486])).

fof(f486,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1778,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK1))))
    | spl34_36 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f1779,plain,
    ( ~ spl34_36
    | spl34_34 ),
    inference(avatar_split_clause,[],[f1774,f1724,f1776])).

fof(f1774,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK1))))
    | spl34_34 ),
    inference(resolution,[],[f1739,f788])).

fof(f788,plain,(
    ! [X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(X0,X1)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_zfmisc_1)).

fof(f1744,plain,
    ( ~ spl34_35
    | spl34_34 ),
    inference(avatar_split_clause,[],[f1738,f1724,f1741])).

fof(f1738,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl34_34 ),
    inference(resolution,[],[f1726,f1053])).

fof(f1734,plain,(
    spl34_33 ),
    inference(avatar_contradiction_clause,[],[f1731])).

fof(f1731,plain,
    ( $false
    | spl34_33 ),
    inference(resolution,[],[f1722,f593])).

fof(f1722,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | spl34_33 ),
    inference(avatar_component_clause,[],[f1720])).

fof(f1720,plain,
    ( spl34_33
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_33])])).

fof(f1728,plain,
    ( ~ spl34_34
    | ~ spl34_33
    | spl34_29 ),
    inference(avatar_split_clause,[],[f1718,f1691,f1720,f1724])).

fof(f1718,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | spl34_29 ),
    inference(extensionality_resolution,[],[f694,f1692])).

fof(f1692,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl34_29 ),
    inference(avatar_component_clause,[],[f1691])).

fof(f1727,plain,
    ( ~ spl34_33
    | ~ spl34_34
    | spl34_29 ),
    inference(avatar_split_clause,[],[f1717,f1691,f1724,f1720])).

fof(f1717,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | spl34_29 ),
    inference(extensionality_resolution,[],[f694,f1692])).

fof(f1713,plain,
    ( spl34_32
    | ~ spl34_3
    | ~ spl34_29 ),
    inference(avatar_split_clause,[],[f1703,f1691,f988,f1710])).

fof(f1710,plain,
    ( spl34_32
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_32])])).

fof(f1703,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl34_3
    | ~ spl34_29 ),
    inference(backward_demodulation,[],[f990,f1693])).

fof(f1708,plain,
    ( ~ spl34_31
    | spl34_26
    | ~ spl34_29 ),
    inference(avatar_split_clause,[],[f1701,f1691,f1623,f1705])).

fof(f1698,plain,
    ( spl34_29
    | spl34_30
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f1689,f988,f1695,f1691])).

fof(f1689,plain,
    ( sP31(sK7(k2_zfmisc_1(sK0,sK1)),sK3,sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl34_3 ),
    inference(resolution,[],[f1637,f578])).

fof(f1637,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | sP31(X0,sK3,sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f974,f990])).

fof(f974,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP31(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f771])).

fof(f771,plain,(
    ! [X2,X0,X3,X1] :
      ( sP31(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f1635,plain,
    ( ~ spl34_27
    | spl34_28
    | ~ spl34_23 ),
    inference(avatar_split_clause,[],[f1617,f1406,f1632,f1628])).

fof(f1617,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ r1_tarski(sK2,sK3)
    | ~ spl34_23 ),
    inference(superposition,[],[f1408,f705])).

fof(f1626,plain,
    ( spl34_25
    | ~ spl34_26
    | ~ spl34_23 ),
    inference(avatar_split_clause,[],[f1616,f1406,f1623,f1619])).

fof(f1619,plain,
    ( spl34_25
  <=> k2_zfmisc_1(sK0,sK1) = k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_25])])).

fof(f1616,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))
    | ~ spl34_23 ),
    inference(resolution,[],[f1408,f694])).

fof(f1581,plain,(
    spl34_13 ),
    inference(avatar_contradiction_clause,[],[f1578])).

fof(f1578,plain,
    ( $false
    | spl34_13 ),
    inference(resolution,[],[f1285,f593])).

fof(f1285,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl34_13 ),
    inference(avatar_component_clause,[],[f1283])).

fof(f1283,plain,
    ( spl34_13
  <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_13])])).

fof(f1417,plain,
    ( ~ spl34_24
    | spl34_20 ),
    inference(avatar_split_clause,[],[f1412,f1317,f1414])).

fof(f1412,plain,
    ( ~ v1_xboole_0(sK2)
    | spl34_20 ),
    inference(resolution,[],[f1319,f1053])).

fof(f1319,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl34_20 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f1409,plain,
    ( spl34_23
    | ~ spl34_3 ),
    inference(avatar_split_clause,[],[f1394,f988,f1406])).

fof(f1394,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))
    | ~ spl34_3 ),
    inference(superposition,[],[f788,f990])).

fof(f1371,plain,
    ( ~ spl34_22
    | spl34_18 ),
    inference(avatar_split_clause,[],[f1365,f1307,f1368])).

fof(f1368,plain,
    ( spl34_22
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_22])])).

fof(f1307,plain,
    ( spl34_18
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_18])])).

fof(f1365,plain,
    ( ~ v1_xboole_0(sK1)
    | spl34_18 ),
    inference(resolution,[],[f1309,f1053])).

fof(f1309,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl34_18 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f1328,plain,
    ( ~ spl34_21
    | spl34_16 ),
    inference(avatar_split_clause,[],[f1322,f1297,f1325])).

fof(f1325,plain,
    ( spl34_21
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_21])])).

fof(f1297,plain,
    ( spl34_16
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_16])])).

fof(f1322,plain,
    ( ~ v1_xboole_0(sK0)
    | spl34_16 ),
    inference(resolution,[],[f1299,f1053])).

fof(f1299,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl34_16 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f1321,plain,
    ( ~ spl34_20
    | ~ spl34_19
    | spl34_5 ),
    inference(avatar_split_clause,[],[f1269,f997,f1313,f1317])).

fof(f1269,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK2,sK0)
    | spl34_5 ),
    inference(extensionality_resolution,[],[f694,f999])).

fof(f1320,plain,
    ( ~ spl34_19
    | ~ spl34_20
    | spl34_5 ),
    inference(avatar_split_clause,[],[f1268,f997,f1317,f1313])).

fof(f1268,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK0,sK2)
    | spl34_5 ),
    inference(extensionality_resolution,[],[f694,f999])).

fof(f1311,plain,
    ( ~ spl34_18
    | ~ spl34_17
    | spl34_1 ),
    inference(avatar_split_clause,[],[f1265,f978,f1303,f1307])).

fof(f1303,plain,
    ( spl34_17
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_17])])).

fof(f1265,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(sK1,k1_xboole_0)
    | spl34_1 ),
    inference(extensionality_resolution,[],[f694,f980])).

fof(f980,plain,
    ( k1_xboole_0 != sK1
    | spl34_1 ),
    inference(avatar_component_clause,[],[f978])).

fof(f1310,plain,
    ( ~ spl34_17
    | ~ spl34_18
    | spl34_1 ),
    inference(avatar_split_clause,[],[f1264,f978,f1307,f1303])).

fof(f1264,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | spl34_1 ),
    inference(extensionality_resolution,[],[f694,f980])).

fof(f1301,plain,
    ( ~ spl34_16
    | ~ spl34_15
    | spl34_2 ),
    inference(avatar_split_clause,[],[f1263,f983,f1293,f1297])).

fof(f1293,plain,
    ( spl34_15
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_15])])).

fof(f1263,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ r1_tarski(sK0,k1_xboole_0)
    | spl34_2 ),
    inference(extensionality_resolution,[],[f694,f985])).

fof(f985,plain,
    ( k1_xboole_0 != sK0
    | spl34_2 ),
    inference(avatar_component_clause,[],[f983])).

fof(f1300,plain,
    ( ~ spl34_15
    | ~ spl34_16
    | spl34_2 ),
    inference(avatar_split_clause,[],[f1262,f983,f1297,f1293])).

fof(f1262,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | spl34_2 ),
    inference(extensionality_resolution,[],[f694,f985])).

fof(f1291,plain,
    ( ~ spl34_14
    | ~ spl34_13
    | spl34_10 ),
    inference(avatar_split_clause,[],[f1261,f1076,f1283,f1287])).

fof(f1287,plain,
    ( spl34_14
  <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_14])])).

fof(f1076,plain,
    ( spl34_10
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_10])])).

fof(f1261,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | spl34_10 ),
    inference(extensionality_resolution,[],[f694,f1078])).

fof(f1078,plain,
    ( k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
    | spl34_10 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f1290,plain,
    ( ~ spl34_13
    | ~ spl34_14
    | spl34_10 ),
    inference(avatar_split_clause,[],[f1260,f1076,f1287,f1283])).

fof(f1260,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl34_10 ),
    inference(extensionality_resolution,[],[f694,f1078])).

fof(f1203,plain,
    ( ~ spl34_12
    | ~ spl34_11 ),
    inference(avatar_split_clause,[],[f1197,f1081,f1200])).

fof(f1200,plain,
    ( spl34_12
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_12])])).

fof(f1081,plain,
    ( spl34_11
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_11])])).

fof(f1197,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl34_11 ),
    inference(resolution,[],[f1151,f1083])).

fof(f1083,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl34_11 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1084,plain,
    ( spl34_11
    | ~ spl34_7 ),
    inference(avatar_split_clause,[],[f1074,f1008,f1081])).

fof(f1074,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl34_7 ),
    inference(superposition,[],[f967,f1010])).

fof(f967,plain,(
    ! [X2] : r2_hidden(X2,k2_tarski(X2,X2)) ),
    inference(equality_resolution,[],[f966])).

fof(f966,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_tarski(X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f886])).

fof(f886,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f688,f729])).

fof(f688,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1079,plain,
    ( ~ spl34_10
    | ~ spl34_7 ),
    inference(avatar_split_clause,[],[f1073,f1008,f1076])).

fof(f1073,plain,
    ( k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
    | ~ spl34_7 ),
    inference(superposition,[],[f1035,f1010])).

fof(f1035,plain,(
    ! [X1] : k1_xboole_0 != k2_tarski(X1,X1) ),
    inference(forward_demodulation,[],[f964,f931])).

fof(f931,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f529])).

fof(f529,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f964,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f875])).

fof(f875,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f681,f729,f729,f729])).

fof(f681,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f353])).

fof(f353,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1021,plain,(
    spl34_9 ),
    inference(avatar_split_clause,[],[f599,f1018])).

fof(f1018,plain,
    ( spl34_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_9])])).

fof(f599,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1016,plain,(
    spl34_8 ),
    inference(avatar_split_clause,[],[f598,f1013])).

fof(f1013,plain,
    ( spl34_8
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_8])])).

fof(f598,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f363])).

fof(f363,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f1011,plain,(
    spl34_7 ),
    inference(avatar_split_clause,[],[f832,f1008])).

fof(f832,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f597,f729])).

fof(f597,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f352])).

fof(f352,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f1005,plain,(
    spl34_6 ),
    inference(avatar_split_clause,[],[f949,f1002])).

fof(f1002,plain,
    ( spl34_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_6])])).

fof(f949,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f585])).

fof(f585,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f455])).

fof(f1000,plain,
    ( ~ spl34_4
    | ~ spl34_5 ),
    inference(avatar_split_clause,[],[f508,f997,f993])).

fof(f508,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f429])).

fof(f429,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f428])).

fof(f428,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f345])).

fof(f345,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f344])).

fof(f344,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f991,plain,(
    spl34_3 ),
    inference(avatar_split_clause,[],[f509,f988])).

fof(f509,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f429])).

fof(f986,plain,(
    ~ spl34_2 ),
    inference(avatar_split_clause,[],[f510,f983])).

fof(f510,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f429])).

fof(f981,plain,(
    ~ spl34_1 ),
    inference(avatar_split_clause,[],[f511,f978])).

fof(f511,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f429])).
%------------------------------------------------------------------------------
