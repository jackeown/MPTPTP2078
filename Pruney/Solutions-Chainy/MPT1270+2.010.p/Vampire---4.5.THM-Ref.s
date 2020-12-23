%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:36 EST 2020

% Result     : Theorem 4.81s
% Output     : Refutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  310 ( 570 expanded)
%              Number of leaves         :   71 ( 246 expanded)
%              Depth                    :    9
%              Number of atoms          :  950 (1692 expanded)
%              Number of equality atoms :  112 ( 174 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f122,f124,f162,f180,f269,f294,f356,f386,f411,f422,f487,f588,f646,f658,f664,f782,f945,f1317,f1437,f1505,f1532,f1554,f1573,f1725,f1801,f1806,f2004,f2233,f2881,f3134,f3203,f3220,f3235,f3248,f3258,f3312,f3347,f3732,f3747,f3763,f4718,f4822,f5471,f5817,f5834])).

fof(f5834,plain,
    ( spl3_4
    | ~ spl3_123
    | ~ spl3_317
    | ~ spl3_477 ),
    inference(avatar_contradiction_clause,[],[f5833])).

fof(f5833,plain,
    ( $false
    | spl3_4
    | ~ spl3_123
    | ~ spl3_317
    | ~ spl3_477 ),
    inference(subsumption_resolution,[],[f5832,f120])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f5832,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_123
    | ~ spl3_317
    | ~ spl3_477 ),
    inference(subsumption_resolution,[],[f5831,f3762])).

fof(f3762,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_317 ),
    inference(avatar_component_clause,[],[f3760])).

fof(f3760,plain,
    ( spl3_317
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_317])])).

fof(f5831,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_123
    | ~ spl3_477 ),
    inference(superposition,[],[f1504,f5800])).

fof(f5800,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_477 ),
    inference(avatar_component_clause,[],[f5798])).

fof(f5798,plain,
    ( spl3_477
  <=> k2_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_477])])).

fof(f1504,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,k2_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)))
        | r1_tarski(sK1,X1) )
    | ~ spl3_123 ),
    inference(avatar_component_clause,[],[f1503])).

fof(f1503,plain,
    ( spl3_123
  <=> ! [X1] :
        ( r1_tarski(sK1,X1)
        | ~ r1_tarski(sK1,k2_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).

fof(f5817,plain,
    ( spl3_477
    | ~ spl3_2
    | ~ spl3_398
    | ~ spl3_464 ),
    inference(avatar_split_clause,[],[f5796,f5469,f4715,f110,f5798])).

fof(f110,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f4715,plain,
    ( spl3_398
  <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_398])])).

fof(f5469,plain,
    ( spl3_464
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_464])])).

fof(f5796,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_398
    | ~ spl3_464 ),
    inference(forward_demodulation,[],[f5790,f4717])).

fof(f4717,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_398 ),
    inference(avatar_component_clause,[],[f4715])).

fof(f5790,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_464 ),
    inference(resolution,[],[f5470,f112])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f5470,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl3_464 ),
    inference(avatar_component_clause,[],[f5469])).

fof(f5471,plain,
    ( spl3_464
    | ~ spl3_66
    | ~ spl3_119 ),
    inference(avatar_split_clause,[],[f1455,f1435,f770,f5469])).

fof(f770,plain,
    ( spl3_66
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f1435,plain,
    ( spl3_119
  <=> ! [X1,X0] :
        ( k2_xboole_0(k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_119])])).

fof(f1455,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl3_66
    | ~ spl3_119 ),
    inference(resolution,[],[f1436,f771])).

fof(f771,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f770])).

fof(f1436,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) )
    | ~ spl3_119 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f4822,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4718,plain,
    ( spl3_398
    | ~ spl3_59
    | ~ spl3_112
    | ~ spl3_316 ),
    inference(avatar_split_clause,[],[f4709,f3744,f1315,f655,f4715])).

fof(f655,plain,
    ( spl3_59
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f1315,plain,
    ( spl3_112
  <=> ! [X11] :
        ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X11) = k4_subset_1(u1_struct_0(sK0),X11,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).

fof(f3744,plain,
    ( spl3_316
  <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_316])])).

fof(f4709,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_59
    | ~ spl3_112
    | ~ spl3_316 ),
    inference(forward_demodulation,[],[f1412,f3746])).

fof(f3746,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_316 ),
    inference(avatar_component_clause,[],[f3744])).

fof(f1412,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_59
    | ~ spl3_112 ),
    inference(resolution,[],[f1316,f656])).

fof(f656,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f655])).

fof(f1316,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X11) = k4_subset_1(u1_struct_0(sK0),X11,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl3_112 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f3763,plain,
    ( spl3_317
    | ~ spl3_2
    | ~ spl3_314 ),
    inference(avatar_split_clause,[],[f3756,f3730,f110,f3760])).

fof(f3730,plain,
    ( spl3_314
  <=> ! [X0] :
        ( r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_314])])).

fof(f3756,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_314 ),
    inference(resolution,[],[f3731,f112])).

fof(f3731,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_struct_0(sK0)) )
    | ~ spl3_314 ),
    inference(avatar_component_clause,[],[f3730])).

fof(f3747,plain,
    ( spl3_316
    | ~ spl3_2
    | ~ spl3_39
    | ~ spl3_128
    | ~ spl3_279 ),
    inference(avatar_split_clause,[],[f3740,f3344,f1530,f484,f110,f3744])).

fof(f484,plain,
    ( spl3_39
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f1530,plain,
    ( spl3_128
  <=> ! [X0] :
        ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).

fof(f3344,plain,
    ( spl3_279
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_279])])).

fof(f3740,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_39
    | ~ spl3_128
    | ~ spl3_279 ),
    inference(forward_demodulation,[],[f1614,f3346])).

fof(f3346,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_279 ),
    inference(avatar_component_clause,[],[f3344])).

fof(f1614,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_39
    | ~ spl3_128 ),
    inference(forward_demodulation,[],[f1608,f486])).

fof(f486,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1608,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_2
    | ~ spl3_128 ),
    inference(resolution,[],[f1531,f112])).

fof(f1531,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_128 ),
    inference(avatar_component_clause,[],[f1530])).

fof(f3732,plain,
    ( spl3_314
    | ~ spl3_285 ),
    inference(avatar_split_clause,[],[f3512,f3464,f3730])).

fof(f3464,plain,
    ( spl3_285
  <=> k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_285])])).

fof(f3512,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_285 ),
    inference(superposition,[],[f240,f3466])).

fof(f3466,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)
    | ~ spl3_285 ),
    inference(avatar_component_clause,[],[f3464])).

fof(f240,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f236,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f236,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f86,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f3347,plain,
    ( spl3_279
    | ~ spl3_1
    | ~ spl3_66
    | ~ spl3_147 ),
    inference(avatar_split_clause,[],[f3339,f1798,f770,f105,f3344])).

fof(f105,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1798,plain,
    ( spl3_147
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).

fof(f3339,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_1
    | ~ spl3_66
    | ~ spl3_147 ),
    inference(subsumption_resolution,[],[f3338,f107])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f3338,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_66
    | ~ spl3_147 ),
    inference(subsumption_resolution,[],[f3337,f771])).

fof(f3337,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_147 ),
    inference(resolution,[],[f1800,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f1800,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_147 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f3312,plain,
    ( spl3_133
    | ~ spl3_278 ),
    inference(avatar_split_clause,[],[f3262,f3256,f1570])).

fof(f1570,plain,
    ( spl3_133
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).

fof(f3256,plain,
    ( spl3_278
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_278])])).

fof(f3262,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_278 ),
    inference(resolution,[],[f3257,f100])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3257,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl3_278 ),
    inference(avatar_component_clause,[],[f3256])).

fof(f3258,plain,
    ( spl3_278
    | ~ spl3_277 ),
    inference(avatar_split_clause,[],[f3253,f3245,f3256])).

fof(f3245,plain,
    ( spl3_277
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_277])])).

fof(f3253,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl3_277 ),
    inference(duplicate_literal_removal,[],[f3250])).

fof(f3250,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl3_277 ),
    inference(resolution,[],[f3247,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f3247,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_277 ),
    inference(avatar_component_clause,[],[f3245])).

fof(f3248,plain,
    ( spl3_277
    | ~ spl3_2
    | ~ spl3_141
    | ~ spl3_276 ),
    inference(avatar_split_clause,[],[f3242,f3233,f1723,f110,f3245])).

fof(f1723,plain,
    ( spl3_141
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP2(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).

fof(f3233,plain,
    ( spl3_276
  <=> ! [X1] :
        ( r1_xboole_0(X1,k1_tops_1(sK0,sK1))
        | sP2(k2_tops_1(sK0,sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_276])])).

fof(f3242,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_141
    | ~ spl3_276 ),
    inference(subsumption_resolution,[],[f3241,f112])).

fof(f3241,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_141
    | ~ spl3_276 ),
    inference(resolution,[],[f3234,f1724])).

fof(f1724,plain,
    ( ! [X1] :
        ( ~ sP2(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_141 ),
    inference(avatar_component_clause,[],[f1723])).

fof(f3234,plain,
    ( ! [X1] :
        ( sP2(k2_tops_1(sK0,sK1),X1)
        | r1_xboole_0(X1,k1_tops_1(sK0,sK1)) )
    | ~ spl3_276 ),
    inference(avatar_component_clause,[],[f3233])).

fof(f3235,plain,
    ( spl3_276
    | ~ spl3_274 ),
    inference(avatar_split_clause,[],[f3229,f3217,f3233])).

fof(f3217,plain,
    ( spl3_274
  <=> r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_274])])).

fof(f3229,plain,
    ( ! [X1] :
        ( r1_xboole_0(X1,k1_tops_1(sK0,sK1))
        | sP2(k2_tops_1(sK0,sK1),X1) )
    | ~ spl3_274 ),
    inference(resolution,[],[f3219,f102])).

fof(f102,plain,(
    ! [X2,X0,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_xboole_0(X0,X2)
      | sP2(X3,X0) ) ),
    inference(cnf_transformation,[],[f102_D])).

fof(f102_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r1_tarski(X2,X3)
          | r1_xboole_0(X0,X2) )
    <=> ~ sP2(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).

fof(f3219,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_274 ),
    inference(avatar_component_clause,[],[f3217])).

fof(f3220,plain,
    ( spl3_274
    | ~ spl3_59
    | ~ spl3_231
    | ~ spl3_272 ),
    inference(avatar_split_clause,[],[f3214,f3200,f2878,f655,f3217])).

fof(f2878,plain,
    ( spl3_231
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_231])])).

fof(f3200,plain,
    ( spl3_272
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_272])])).

fof(f3214,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_59
    | ~ spl3_231
    | ~ spl3_272 ),
    inference(subsumption_resolution,[],[f3213,f2880])).

fof(f2880,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_231 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f3213,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_59
    | ~ spl3_272 ),
    inference(subsumption_resolution,[],[f3209,f656])).

fof(f3209,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_272 ),
    inference(resolution,[],[f3202,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f3202,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl3_272 ),
    inference(avatar_component_clause,[],[f3200])).

fof(f3203,plain,
    ( spl3_272
    | ~ spl3_11
    | ~ spl3_263 ),
    inference(avatar_split_clause,[],[f3191,f3132,f177,f3200])).

fof(f177,plain,
    ( spl3_11
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f3132,plain,
    ( spl3_263
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_263])])).

fof(f3191,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl3_11
    | ~ spl3_263 ),
    inference(resolution,[],[f3133,f179])).

fof(f179,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f3133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) )
    | ~ spl3_263 ),
    inference(avatar_component_clause,[],[f3132])).

fof(f3134,plain,
    ( spl3_263
    | ~ spl3_132 ),
    inference(avatar_split_clause,[],[f1686,f1552,f3132])).

fof(f1552,plain,
    ( spl3_132
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | ~ sP2(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_132])])).

fof(f1686,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) )
    | ~ spl3_132 ),
    inference(resolution,[],[f1553,f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( sP2(X3,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f102,f100])).

fof(f1553,plain,
    ( ! [X2] :
        ( ~ sP2(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl3_132 ),
    inference(avatar_component_clause,[],[f1552])).

fof(f2881,plain,
    ( spl3_231
    | ~ spl3_51
    | ~ spl3_169
    | ~ spl3_182 ),
    inference(avatar_split_clause,[],[f2876,f2230,f2001,f585,f2878])).

fof(f585,plain,
    ( spl3_51
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f2001,plain,
    ( spl3_169
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_169])])).

fof(f2230,plain,
    ( spl3_182
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_182])])).

fof(f2876,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_51
    | ~ spl3_169
    | ~ spl3_182 ),
    inference(subsumption_resolution,[],[f2875,f2232])).

fof(f2232,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_182 ),
    inference(avatar_component_clause,[],[f2230])).

fof(f2875,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_51
    | ~ spl3_169 ),
    inference(forward_demodulation,[],[f596,f2003])).

fof(f2003,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl3_169 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f596,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_51 ),
    inference(superposition,[],[f84,f587])).

fof(f587,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f585])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2233,plain,
    ( spl3_182
    | ~ spl3_1
    | ~ spl3_66
    | ~ spl3_169 ),
    inference(avatar_split_clause,[],[f2184,f2001,f770,f105,f2230])).

fof(f2184,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_66
    | ~ spl3_169 ),
    inference(subsumption_resolution,[],[f2183,f107])).

fof(f2183,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_66
    | ~ spl3_169 ),
    inference(subsumption_resolution,[],[f2177,f771])).

fof(f2177,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_169 ),
    inference(superposition,[],[f89,f2003])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2004,plain,
    ( spl3_169
    | ~ spl3_51
    | ~ spl3_66
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f1007,f943,f770,f585,f2001])).

fof(f943,plain,
    ( spl3_78
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f1007,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl3_51
    | ~ spl3_66
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f1000,f587])).

fof(f1000,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl3_66
    | ~ spl3_78 ),
    inference(resolution,[],[f944,f771])).

fof(f944,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) )
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f943])).

fof(f1806,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_133 ),
    inference(avatar_contradiction_clause,[],[f1805])).

fof(f1805,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_133 ),
    inference(unit_resulting_resolution,[],[f107,f112,f1572,f116,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f116,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_3
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1572,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_133 ),
    inference(avatar_component_clause,[],[f1570])).

fof(f1801,plain,
    ( spl3_147
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1772,f115,f110,f105,f1798])).

fof(f1772,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f1771,f107])).

fof(f1771,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f1769,f112])).

fof(f1769,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f117,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f117,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1725,plain,
    ( spl3_141
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f703,f644,f1723])).

fof(f644,plain,
    ( spl3_57
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X5,k1_tops_1(sK0,X4))
        | ~ sP2(k2_tops_1(sK0,X4),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f703,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP2(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) )
    | ~ spl3_57 ),
    inference(resolution,[],[f645,f100])).

fof(f645,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X5,k1_tops_1(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP2(k2_tops_1(sK0,X4),X5) )
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f644])).

fof(f1573,plain,
    ( spl3_133
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1560,f115,f110,f105,f1570])).

fof(f1560,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f1559,f107])).

fof(f1559,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f1556,f112])).

fof(f1556,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f117,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1554,plain,
    ( spl3_132
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f696,f651,f1552])).

fof(f651,plain,
    ( spl3_58
  <=> r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f696,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | ~ sP2(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2) )
    | ~ spl3_58 ),
    inference(resolution,[],[f653,f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X0,X1)
      | ~ sP2(X3,X0) ) ),
    inference(general_splitting,[],[f99,f102_D])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f653,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f651])).

fof(f1532,plain,
    ( spl3_128
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f398,f384,f1530])).

fof(f384,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f398,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(resolution,[],[f385,f84])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1505,plain,
    ( spl3_123
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f288,f266,f1503])).

fof(f266,plain,
    ( spl3_16
  <=> r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f288,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,X1)
        | ~ r1_tarski(sK1,k2_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl3_16 ),
    inference(resolution,[],[f268,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f268,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f266])).

fof(f1437,plain,
    ( spl3_119
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f461,f105,f1435])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f215,f107])).

fof(f215,plain,(
    ! [X10,X8,X9] :
      ( ~ l1_pre_topc(X9)
      | k2_xboole_0(k2_tops_1(X9,X10),X8) = k4_subset_1(u1_struct_0(X9),k2_tops_1(X9,X10),X8)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(resolution,[],[f96,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1317,plain,
    ( spl3_112
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f459,f110,f1315])).

fof(f459,plain,
    ( ! [X11] :
        ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X11) = k4_subset_1(u1_struct_0(sK0),X11,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f228,f112])).

fof(f228,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k4_subset_1(X3,k3_subset_1(X3,X4),X2) = k4_subset_1(X3,X2,k3_subset_1(X3,X4))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f97,f84])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f945,plain,
    ( spl3_78
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f438,f105,f943])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f158,f107])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f89,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f782,plain,
    ( ~ spl3_2
    | spl3_66 ),
    inference(avatar_contradiction_clause,[],[f781])).

fof(f781,plain,
    ( $false
    | ~ spl3_2
    | spl3_66 ),
    inference(subsumption_resolution,[],[f779,f112])).

fof(f779,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_66 ),
    inference(resolution,[],[f772,f84])).

fof(f772,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_66 ),
    inference(avatar_component_clause,[],[f770])).

fof(f664,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_59 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_59 ),
    inference(subsumption_resolution,[],[f662,f107])).

fof(f662,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | spl3_59 ),
    inference(subsumption_resolution,[],[f660,f112])).

fof(f660,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_59 ),
    inference(resolution,[],[f657,f90])).

fof(f657,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f655])).

fof(f658,plain,
    ( spl3_58
    | ~ spl3_59
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f414,f409,f110,f655,f651])).

fof(f409,plain,
    ( spl3_29
  <=> ! [X4] :
        ( r1_xboole_0(sK1,k3_subset_1(X4,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X4))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f414,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(resolution,[],[f410,f112])).

fof(f410,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X4))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X4))
        | r1_xboole_0(sK1,k3_subset_1(X4,k2_tops_1(sK0,sK1))) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f409])).

fof(f646,plain,
    ( spl3_57
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f301,f292,f644])).

fof(f292,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f301,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X5,k1_tops_1(sK0,X4))
        | ~ sP2(k2_tops_1(sK0,X4),X5) )
    | ~ spl3_18 ),
    inference(resolution,[],[f293,f103])).

fof(f293,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f292])).

fof(f588,plain,
    ( spl3_51
    | ~ spl3_2
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f429,f420,f110,f585])).

fof(f420,plain,
    ( spl3_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f429,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_2
    | ~ spl3_31 ),
    inference(resolution,[],[f421,f112])).

fof(f421,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f420])).

fof(f487,plain,
    ( spl3_39
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f361,f354,f110,f484])).

fof(f354,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f361,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(resolution,[],[f355,f112])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f354])).

fof(f422,plain,
    ( spl3_31
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f246,f105,f420])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f107])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f411,plain,
    ( spl3_29
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f203,f119,f409])).

fof(f203,plain,
    ( ! [X4] :
        ( r1_xboole_0(sK1,k3_subset_1(X4,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X4))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X4)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f88,f121])).

fof(f121,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f386,plain,
    ( spl3_27
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f234,f105,f384])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f76,f107])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f356,plain,
    ( spl3_23
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f221,f105,f354])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f75,f107])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f294,plain,
    ( spl3_18
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f157,f105,f292])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f74,f107])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(f269,plain,
    ( spl3_16
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f254,f110,f266])).

fof(f254,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f205,f112])).

fof(f205,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | r1_xboole_0(X2,k3_subset_1(X3,X2)) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k3_subset_1(X3,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f88,f100])).

fof(f180,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f168,f160,f110,f177])).

fof(f160,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f168,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f161,f112])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f146,f105,f160])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f73,f107])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f124,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f123,f119,f115])).

fof(f123,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f70,f121])).

fof(f70,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f122,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f69,f119,f115])).

fof(f69,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f68,f110])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f108,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f67,f105])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:12:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (20950)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (20958)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (20951)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (20974)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (20953)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (20955)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (20956)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (20954)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (20969)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (20967)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (20963)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (20960)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (20973)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (20961)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (20975)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (20968)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (20970)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (20952)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (20971)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (20965)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (20972)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.38/0.54  % (20959)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.54  % (20957)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.38/0.54  % (20964)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.38/0.55  % (20962)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.51/0.56  % (20966)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.41/0.70  % (20959)Refutation not found, incomplete strategy% (20959)------------------------------
% 2.41/0.70  % (20959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.41/0.70  % (20959)Termination reason: Refutation not found, incomplete strategy
% 2.41/0.70  
% 2.41/0.70  % (20959)Memory used [KB]: 6140
% 2.41/0.70  % (20959)Time elapsed: 0.293 s
% 2.41/0.70  % (20959)------------------------------
% 2.41/0.70  % (20959)------------------------------
% 3.85/0.90  % (20964)Time limit reached!
% 3.85/0.90  % (20964)------------------------------
% 3.85/0.90  % (20964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.90  % (20964)Termination reason: Time limit
% 3.85/0.90  % (20964)Termination phase: Saturation
% 3.85/0.90  
% 3.85/0.90  % (20964)Memory used [KB]: 7547
% 3.85/0.90  % (20964)Time elapsed: 0.500 s
% 3.85/0.90  % (20964)------------------------------
% 3.85/0.90  % (20964)------------------------------
% 3.85/0.90  % (20963)Time limit reached!
% 3.85/0.90  % (20963)------------------------------
% 3.85/0.90  % (20963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.90  % (20963)Termination reason: Time limit
% 3.85/0.90  
% 3.85/0.90  % (20963)Memory used [KB]: 9466
% 3.85/0.90  % (20963)Time elapsed: 0.501 s
% 3.85/0.90  % (20963)------------------------------
% 3.85/0.90  % (20963)------------------------------
% 3.85/0.92  % (20950)Time limit reached!
% 3.85/0.92  % (20950)------------------------------
% 3.85/0.92  % (20950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.92  % (20950)Termination reason: Time limit
% 3.85/0.92  % (20950)Termination phase: Saturation
% 3.85/0.92  
% 3.85/0.92  % (20950)Memory used [KB]: 17142
% 3.85/0.92  % (20950)Time elapsed: 0.500 s
% 3.85/0.92  % (20950)------------------------------
% 3.85/0.92  % (20950)------------------------------
% 4.81/1.00  % (20952)Refutation found. Thanks to Tanya!
% 4.81/1.00  % SZS status Theorem for theBenchmark
% 4.81/1.00  % SZS output start Proof for theBenchmark
% 4.81/1.00  fof(f5835,plain,(
% 4.81/1.00    $false),
% 4.81/1.00    inference(avatar_sat_refutation,[],[f108,f113,f122,f124,f162,f180,f269,f294,f356,f386,f411,f422,f487,f588,f646,f658,f664,f782,f945,f1317,f1437,f1505,f1532,f1554,f1573,f1725,f1801,f1806,f2004,f2233,f2881,f3134,f3203,f3220,f3235,f3248,f3258,f3312,f3347,f3732,f3747,f3763,f4718,f4822,f5471,f5817,f5834])).
% 4.81/1.00  fof(f5834,plain,(
% 4.81/1.00    spl3_4 | ~spl3_123 | ~spl3_317 | ~spl3_477),
% 4.81/1.00    inference(avatar_contradiction_clause,[],[f5833])).
% 4.81/1.00  fof(f5833,plain,(
% 4.81/1.00    $false | (spl3_4 | ~spl3_123 | ~spl3_317 | ~spl3_477)),
% 4.81/1.00    inference(subsumption_resolution,[],[f5832,f120])).
% 4.81/1.00  fof(f120,plain,(
% 4.81/1.00    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | spl3_4),
% 4.81/1.00    inference(avatar_component_clause,[],[f119])).
% 4.81/1.00  fof(f119,plain,(
% 4.81/1.00    spl3_4 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.81/1.00  fof(f5832,plain,(
% 4.81/1.00    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl3_123 | ~spl3_317 | ~spl3_477)),
% 4.81/1.00    inference(subsumption_resolution,[],[f5831,f3762])).
% 4.81/1.00  fof(f3762,plain,(
% 4.81/1.00    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_317),
% 4.81/1.00    inference(avatar_component_clause,[],[f3760])).
% 4.81/1.00  fof(f3760,plain,(
% 4.81/1.00    spl3_317 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_317])])).
% 4.81/1.00  fof(f5831,plain,(
% 4.81/1.00    ~r1_tarski(sK1,k2_struct_0(sK0)) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl3_123 | ~spl3_477)),
% 4.81/1.00    inference(superposition,[],[f1504,f5800])).
% 4.81/1.00  fof(f5800,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_477),
% 4.81/1.00    inference(avatar_component_clause,[],[f5798])).
% 4.81/1.00  fof(f5798,plain,(
% 4.81/1.00    spl3_477 <=> k2_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_477])])).
% 4.81/1.00  fof(f1504,plain,(
% 4.81/1.00    ( ! [X1] : (~r1_tarski(sK1,k2_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1))) | r1_tarski(sK1,X1)) ) | ~spl3_123),
% 4.81/1.00    inference(avatar_component_clause,[],[f1503])).
% 4.81/1.00  fof(f1503,plain,(
% 4.81/1.00    spl3_123 <=> ! [X1] : (r1_tarski(sK1,X1) | ~r1_tarski(sK1,k2_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).
% 4.81/1.00  fof(f5817,plain,(
% 4.81/1.00    spl3_477 | ~spl3_2 | ~spl3_398 | ~spl3_464),
% 4.81/1.00    inference(avatar_split_clause,[],[f5796,f5469,f4715,f110,f5798])).
% 4.81/1.00  fof(f110,plain,(
% 4.81/1.00    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.81/1.00  fof(f4715,plain,(
% 4.81/1.00    spl3_398 <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_398])])).
% 4.81/1.00  fof(f5469,plain,(
% 4.81/1.00    spl3_464 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_464])])).
% 4.81/1.00  fof(f5796,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_398 | ~spl3_464)),
% 4.81/1.00    inference(forward_demodulation,[],[f5790,f4717])).
% 4.81/1.00  fof(f4717,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_398),
% 4.81/1.00    inference(avatar_component_clause,[],[f4715])).
% 4.81/1.00  fof(f5790,plain,(
% 4.81/1.00    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_464)),
% 4.81/1.00    inference(resolution,[],[f5470,f112])).
% 4.81/1.00  fof(f112,plain,(
% 4.81/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.81/1.00    inference(avatar_component_clause,[],[f110])).
% 4.81/1.00  fof(f5470,plain,(
% 4.81/1.00    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1))) ) | ~spl3_464),
% 4.81/1.00    inference(avatar_component_clause,[],[f5469])).
% 4.81/1.00  fof(f5471,plain,(
% 4.81/1.00    spl3_464 | ~spl3_66 | ~spl3_119),
% 4.81/1.00    inference(avatar_split_clause,[],[f1455,f1435,f770,f5469])).
% 4.81/1.00  fof(f770,plain,(
% 4.81/1.00    spl3_66 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 4.81/1.00  fof(f1435,plain,(
% 4.81/1.00    spl3_119 <=> ! [X1,X0] : (k2_xboole_0(k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_119])])).
% 4.81/1.00  fof(f1455,plain,(
% 4.81/1.00    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k3_subset_1(u1_struct_0(sK0),sK1))) ) | (~spl3_66 | ~spl3_119)),
% 4.81/1.00    inference(resolution,[],[f1436,f771])).
% 4.81/1.00  fof(f771,plain,(
% 4.81/1.00    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_66),
% 4.81/1.00    inference(avatar_component_clause,[],[f770])).
% 4.81/1.00  fof(f1436,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1)) ) | ~spl3_119),
% 4.81/1.00    inference(avatar_component_clause,[],[f1435])).
% 4.81/1.00  fof(f4822,plain,(
% 4.81/1.00    k1_xboole_0 != k1_tops_1(sK0,sK1) | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)),
% 4.81/1.00    introduced(theory_tautology_sat_conflict,[])).
% 4.81/1.00  fof(f4718,plain,(
% 4.81/1.00    spl3_398 | ~spl3_59 | ~spl3_112 | ~spl3_316),
% 4.81/1.00    inference(avatar_split_clause,[],[f4709,f3744,f1315,f655,f4715])).
% 4.81/1.00  fof(f655,plain,(
% 4.81/1.00    spl3_59 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 4.81/1.00  fof(f1315,plain,(
% 4.81/1.00    spl3_112 <=> ! [X11] : (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X11) = k4_subset_1(u1_struct_0(sK0),X11,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).
% 4.81/1.00  fof(f3744,plain,(
% 4.81/1.00    spl3_316 <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_316])])).
% 4.81/1.00  fof(f4709,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_59 | ~spl3_112 | ~spl3_316)),
% 4.81/1.00    inference(forward_demodulation,[],[f1412,f3746])).
% 4.81/1.00  fof(f3746,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl3_316),
% 4.81/1.00    inference(avatar_component_clause,[],[f3744])).
% 4.81/1.00  fof(f1412,plain,(
% 4.81/1.00    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_59 | ~spl3_112)),
% 4.81/1.00    inference(resolution,[],[f1316,f656])).
% 4.81/1.00  fof(f656,plain,(
% 4.81/1.00    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_59),
% 4.81/1.00    inference(avatar_component_clause,[],[f655])).
% 4.81/1.00  fof(f1316,plain,(
% 4.81/1.00    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X11) = k4_subset_1(u1_struct_0(sK0),X11,k3_subset_1(u1_struct_0(sK0),sK1))) ) | ~spl3_112),
% 4.81/1.00    inference(avatar_component_clause,[],[f1315])).
% 4.81/1.00  fof(f3763,plain,(
% 4.81/1.00    spl3_317 | ~spl3_2 | ~spl3_314),
% 4.81/1.00    inference(avatar_split_clause,[],[f3756,f3730,f110,f3760])).
% 4.81/1.00  fof(f3730,plain,(
% 4.81/1.00    spl3_314 <=> ! [X0] : (r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_314])])).
% 4.81/1.00  fof(f3756,plain,(
% 4.81/1.00    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_2 | ~spl3_314)),
% 4.81/1.00    inference(resolution,[],[f3731,f112])).
% 4.81/1.00  fof(f3731,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_struct_0(sK0))) ) | ~spl3_314),
% 4.81/1.00    inference(avatar_component_clause,[],[f3730])).
% 4.81/1.00  fof(f3747,plain,(
% 4.81/1.00    spl3_316 | ~spl3_2 | ~spl3_39 | ~spl3_128 | ~spl3_279),
% 4.81/1.00    inference(avatar_split_clause,[],[f3740,f3344,f1530,f484,f110,f3744])).
% 4.81/1.00  fof(f484,plain,(
% 4.81/1.00    spl3_39 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 4.81/1.00  fof(f1530,plain,(
% 4.81/1.00    spl3_128 <=> ! [X0] : (k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).
% 4.81/1.00  fof(f3344,plain,(
% 4.81/1.00    spl3_279 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_279])])).
% 4.81/1.00  fof(f3740,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_39 | ~spl3_128 | ~spl3_279)),
% 4.81/1.00    inference(forward_demodulation,[],[f1614,f3346])).
% 4.81/1.00  fof(f3346,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_279),
% 4.81/1.00    inference(avatar_component_clause,[],[f3344])).
% 4.81/1.00  fof(f1614,plain,(
% 4.81/1.00    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_39 | ~spl3_128)),
% 4.81/1.00    inference(forward_demodulation,[],[f1608,f486])).
% 4.81/1.00  fof(f486,plain,(
% 4.81/1.00    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_39),
% 4.81/1.00    inference(avatar_component_clause,[],[f484])).
% 4.81/1.00  fof(f1608,plain,(
% 4.81/1.00    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_2 | ~spl3_128)),
% 4.81/1.00    inference(resolution,[],[f1531,f112])).
% 4.81/1.00  fof(f1531,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl3_128),
% 4.81/1.00    inference(avatar_component_clause,[],[f1530])).
% 4.81/1.00  fof(f3732,plain,(
% 4.81/1.00    spl3_314 | ~spl3_285),
% 4.81/1.00    inference(avatar_split_clause,[],[f3512,f3464,f3730])).
% 4.81/1.00  fof(f3464,plain,(
% 4.81/1.00    spl3_285 <=> k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_285])])).
% 4.81/1.00  fof(f3512,plain,(
% 4.81/1.00    ( ! [X0] : (r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_285),
% 4.81/1.00    inference(superposition,[],[f240,f3466])).
% 4.81/1.00  fof(f3466,plain,(
% 4.81/1.00    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) | ~spl3_285),
% 4.81/1.00    inference(avatar_component_clause,[],[f3464])).
% 4.81/1.00  fof(f240,plain,(
% 4.81/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.81/1.00    inference(subsumption_resolution,[],[f236,f72])).
% 4.81/1.00  fof(f72,plain,(
% 4.81/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f12])).
% 4.81/1.00  fof(f12,axiom,(
% 4.81/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 4.81/1.00  fof(f236,plain,(
% 4.81/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 4.81/1.00    inference(resolution,[],[f86,f71])).
% 4.81/1.00  fof(f71,plain,(
% 4.81/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f2])).
% 4.81/1.00  fof(f2,axiom,(
% 4.81/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.81/1.00  fof(f86,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f38])).
% 4.81/1.00  fof(f38,plain,(
% 4.81/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(flattening,[],[f37])).
% 4.81/1.00  fof(f37,plain,(
% 4.81/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(ennf_transformation,[],[f10])).
% 4.81/1.00  fof(f10,axiom,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 4.81/1.00  fof(f3347,plain,(
% 4.81/1.00    spl3_279 | ~spl3_1 | ~spl3_66 | ~spl3_147),
% 4.81/1.00    inference(avatar_split_clause,[],[f3339,f1798,f770,f105,f3344])).
% 4.81/1.00  fof(f105,plain,(
% 4.81/1.00    spl3_1 <=> l1_pre_topc(sK0)),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.81/1.00  fof(f1798,plain,(
% 4.81/1.00    spl3_147 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).
% 4.81/1.00  fof(f3339,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_1 | ~spl3_66 | ~spl3_147)),
% 4.81/1.00    inference(subsumption_resolution,[],[f3338,f107])).
% 4.81/1.00  fof(f107,plain,(
% 4.81/1.00    l1_pre_topc(sK0) | ~spl3_1),
% 4.81/1.00    inference(avatar_component_clause,[],[f105])).
% 4.81/1.00  fof(f3338,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl3_66 | ~spl3_147)),
% 4.81/1.00    inference(subsumption_resolution,[],[f3337,f771])).
% 4.81/1.00  fof(f3337,plain,(
% 4.81/1.00    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_147),
% 4.81/1.00    inference(resolution,[],[f1800,f78])).
% 4.81/1.00  fof(f78,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f61])).
% 4.81/1.00  fof(f61,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(nnf_transformation,[],[f32])).
% 4.81/1.00  fof(f32,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f16])).
% 4.81/1.00  fof(f16,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 4.81/1.00  fof(f1800,plain,(
% 4.81/1.00    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_147),
% 4.81/1.00    inference(avatar_component_clause,[],[f1798])).
% 4.81/1.00  fof(f3312,plain,(
% 4.81/1.00    spl3_133 | ~spl3_278),
% 4.81/1.00    inference(avatar_split_clause,[],[f3262,f3256,f1570])).
% 4.81/1.00  fof(f1570,plain,(
% 4.81/1.00    spl3_133 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).
% 4.81/1.00  fof(f3256,plain,(
% 4.81/1.00    spl3_278 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tops_1(sK0,sK1)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_278])])).
% 4.81/1.00  fof(f3262,plain,(
% 4.81/1.00    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_278),
% 4.81/1.00    inference(resolution,[],[f3257,f100])).
% 4.81/1.00  fof(f100,plain,(
% 4.81/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.81/1.00    inference(equality_resolution,[],[f92])).
% 4.81/1.00  fof(f92,plain,(
% 4.81/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.81/1.00    inference(cnf_transformation,[],[f66])).
% 4.81/1.00  fof(f66,plain,(
% 4.81/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.81/1.00    inference(flattening,[],[f65])).
% 4.81/1.00  fof(f65,plain,(
% 4.81/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.81/1.00    inference(nnf_transformation,[],[f1])).
% 4.81/1.00  fof(f1,axiom,(
% 4.81/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.81/1.00  fof(f3257,plain,(
% 4.81/1.00    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,sK1)) | k1_xboole_0 = X0) ) | ~spl3_278),
% 4.81/1.00    inference(avatar_component_clause,[],[f3256])).
% 4.81/1.00  fof(f3258,plain,(
% 4.81/1.00    spl3_278 | ~spl3_277),
% 4.81/1.00    inference(avatar_split_clause,[],[f3253,f3245,f3256])).
% 4.81/1.00  fof(f3245,plain,(
% 4.81/1.00    spl3_277 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_277])])).
% 4.81/1.00  fof(f3253,plain,(
% 4.81/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | ~spl3_277),
% 4.81/1.00    inference(duplicate_literal_removal,[],[f3250])).
% 4.81/1.00  fof(f3250,plain,(
% 4.81/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | ~spl3_277),
% 4.81/1.00    inference(resolution,[],[f3247,f95])).
% 4.81/1.00  fof(f95,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f47])).
% 4.81/1.00  fof(f47,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 4.81/1.00    inference(flattening,[],[f46])).
% 4.81/1.00  fof(f46,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 4.81/1.00    inference(ennf_transformation,[],[f4])).
% 4.81/1.00  fof(f4,axiom,(
% 4.81/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 4.81/1.00  fof(f3247,plain,(
% 4.81/1.00    r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_277),
% 4.81/1.00    inference(avatar_component_clause,[],[f3245])).
% 4.81/1.00  fof(f3248,plain,(
% 4.81/1.00    spl3_277 | ~spl3_2 | ~spl3_141 | ~spl3_276),
% 4.81/1.00    inference(avatar_split_clause,[],[f3242,f3233,f1723,f110,f3245])).
% 4.81/1.00  fof(f1723,plain,(
% 4.81/1.00    spl3_141 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~sP2(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).
% 4.81/1.00  fof(f3233,plain,(
% 4.81/1.00    spl3_276 <=> ! [X1] : (r1_xboole_0(X1,k1_tops_1(sK0,sK1)) | sP2(k2_tops_1(sK0,sK1),X1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_276])])).
% 4.81/1.00  fof(f3242,plain,(
% 4.81/1.00    r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_141 | ~spl3_276)),
% 4.81/1.00    inference(subsumption_resolution,[],[f3241,f112])).
% 4.81/1.00  fof(f3241,plain,(
% 4.81/1.00    r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_141 | ~spl3_276)),
% 4.81/1.00    inference(resolution,[],[f3234,f1724])).
% 4.81/1.00  fof(f1724,plain,(
% 4.81/1.00    ( ! [X1] : (~sP2(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_141),
% 4.81/1.00    inference(avatar_component_clause,[],[f1723])).
% 4.81/1.00  fof(f3234,plain,(
% 4.81/1.00    ( ! [X1] : (sP2(k2_tops_1(sK0,sK1),X1) | r1_xboole_0(X1,k1_tops_1(sK0,sK1))) ) | ~spl3_276),
% 4.81/1.00    inference(avatar_component_clause,[],[f3233])).
% 4.81/1.00  fof(f3235,plain,(
% 4.81/1.00    spl3_276 | ~spl3_274),
% 4.81/1.00    inference(avatar_split_clause,[],[f3229,f3217,f3233])).
% 4.81/1.00  fof(f3217,plain,(
% 4.81/1.00    spl3_274 <=> r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_274])])).
% 4.81/1.00  fof(f3229,plain,(
% 4.81/1.00    ( ! [X1] : (r1_xboole_0(X1,k1_tops_1(sK0,sK1)) | sP2(k2_tops_1(sK0,sK1),X1)) ) | ~spl3_274),
% 4.81/1.00    inference(resolution,[],[f3219,f102])).
% 4.81/1.00  fof(f102,plain,(
% 4.81/1.00    ( ! [X2,X0,X3] : (~r1_tarski(X2,X3) | r1_xboole_0(X0,X2) | sP2(X3,X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f102_D])).
% 4.81/1.00  fof(f102_D,plain,(
% 4.81/1.00    ( ! [X0,X3] : (( ! [X2] : (~r1_tarski(X2,X3) | r1_xboole_0(X0,X2)) ) <=> ~sP2(X3,X0)) )),
% 4.81/1.00    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
% 4.81/1.00  fof(f3219,plain,(
% 4.81/1.00    r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_274),
% 4.81/1.00    inference(avatar_component_clause,[],[f3217])).
% 4.81/1.00  fof(f3220,plain,(
% 4.81/1.00    spl3_274 | ~spl3_59 | ~spl3_231 | ~spl3_272),
% 4.81/1.00    inference(avatar_split_clause,[],[f3214,f3200,f2878,f655,f3217])).
% 4.81/1.00  fof(f2878,plain,(
% 4.81/1.00    spl3_231 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_231])])).
% 4.81/1.00  fof(f3200,plain,(
% 4.81/1.00    spl3_272 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_272])])).
% 4.81/1.00  fof(f3214,plain,(
% 4.81/1.00    r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_59 | ~spl3_231 | ~spl3_272)),
% 4.81/1.00    inference(subsumption_resolution,[],[f3213,f2880])).
% 4.81/1.00  fof(f2880,plain,(
% 4.81/1.00    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_231),
% 4.81/1.00    inference(avatar_component_clause,[],[f2878])).
% 4.81/1.00  fof(f3213,plain,(
% 4.81/1.00    r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_59 | ~spl3_272)),
% 4.81/1.00    inference(subsumption_resolution,[],[f3209,f656])).
% 4.81/1.00  fof(f3209,plain,(
% 4.81/1.00    r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_272),
% 4.81/1.00    inference(resolution,[],[f3202,f87])).
% 4.81/1.00  fof(f87,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f64])).
% 4.81/1.00  fof(f64,plain,(
% 4.81/1.00    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(nnf_transformation,[],[f39])).
% 4.81/1.00  fof(f39,plain,(
% 4.81/1.00    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(ennf_transformation,[],[f11])).
% 4.81/1.00  fof(f11,axiom,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 4.81/1.00  fof(f3202,plain,(
% 4.81/1.00    r1_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl3_272),
% 4.81/1.00    inference(avatar_component_clause,[],[f3200])).
% 4.81/1.00  fof(f3203,plain,(
% 4.81/1.00    spl3_272 | ~spl3_11 | ~spl3_263),
% 4.81/1.00    inference(avatar_split_clause,[],[f3191,f3132,f177,f3200])).
% 4.81/1.00  fof(f177,plain,(
% 4.81/1.00    spl3_11 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 4.81/1.00  fof(f3132,plain,(
% 4.81/1.00    spl3_263 <=> ! [X0] : (~r1_tarski(X0,sK1) | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_263])])).
% 4.81/1.00  fof(f3191,plain,(
% 4.81/1.00    r1_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl3_11 | ~spl3_263)),
% 4.81/1.00    inference(resolution,[],[f3133,f179])).
% 4.81/1.00  fof(f179,plain,(
% 4.81/1.00    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_11),
% 4.81/1.00    inference(avatar_component_clause,[],[f177])).
% 4.81/1.00  fof(f3133,plain,(
% 4.81/1.00    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ) | ~spl3_263),
% 4.81/1.00    inference(avatar_component_clause,[],[f3132])).
% 4.81/1.00  fof(f3134,plain,(
% 4.81/1.00    spl3_263 | ~spl3_132),
% 4.81/1.00    inference(avatar_split_clause,[],[f1686,f1552,f3132])).
% 4.81/1.00  fof(f1552,plain,(
% 4.81/1.00    spl3_132 <=> ! [X2] : (~r1_tarski(X2,sK1) | ~sP2(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_132])])).
% 4.81/1.00  fof(f1686,plain,(
% 4.81/1.00    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ) | ~spl3_132),
% 4.81/1.00    inference(resolution,[],[f1553,f131])).
% 4.81/1.00  fof(f131,plain,(
% 4.81/1.00    ( ! [X2,X3] : (sP2(X3,X2) | r1_xboole_0(X2,X3)) )),
% 4.81/1.00    inference(resolution,[],[f102,f100])).
% 4.81/1.00  fof(f1553,plain,(
% 4.81/1.00    ( ! [X2] : (~sP2(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2) | ~r1_tarski(X2,sK1)) ) | ~spl3_132),
% 4.81/1.00    inference(avatar_component_clause,[],[f1552])).
% 4.81/1.00  fof(f2881,plain,(
% 4.81/1.00    spl3_231 | ~spl3_51 | ~spl3_169 | ~spl3_182),
% 4.81/1.00    inference(avatar_split_clause,[],[f2876,f2230,f2001,f585,f2878])).
% 4.81/1.00  fof(f585,plain,(
% 4.81/1.00    spl3_51 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 4.81/1.00  fof(f2001,plain,(
% 4.81/1.00    spl3_169 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_169])])).
% 4.81/1.00  fof(f2230,plain,(
% 4.81/1.00    spl3_182 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_182])])).
% 4.81/1.00  fof(f2876,plain,(
% 4.81/1.00    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_51 | ~spl3_169 | ~spl3_182)),
% 4.81/1.00    inference(subsumption_resolution,[],[f2875,f2232])).
% 4.81/1.00  fof(f2232,plain,(
% 4.81/1.00    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_182),
% 4.81/1.00    inference(avatar_component_clause,[],[f2230])).
% 4.81/1.00  fof(f2875,plain,(
% 4.81/1.00    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_51 | ~spl3_169)),
% 4.81/1.00    inference(forward_demodulation,[],[f596,f2003])).
% 4.81/1.00  fof(f2003,plain,(
% 4.81/1.00    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl3_169),
% 4.81/1.00    inference(avatar_component_clause,[],[f2001])).
% 4.81/1.00  fof(f596,plain,(
% 4.81/1.00    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_51),
% 4.81/1.00    inference(superposition,[],[f84,f587])).
% 4.81/1.00  fof(f587,plain,(
% 4.81/1.00    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl3_51),
% 4.81/1.00    inference(avatar_component_clause,[],[f585])).
% 4.81/1.00  fof(f84,plain,(
% 4.81/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f35])).
% 4.81/1.00  fof(f35,plain,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(ennf_transformation,[],[f7])).
% 4.81/1.00  fof(f7,axiom,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.81/1.00  fof(f2233,plain,(
% 4.81/1.00    spl3_182 | ~spl3_1 | ~spl3_66 | ~spl3_169),
% 4.81/1.00    inference(avatar_split_clause,[],[f2184,f2001,f770,f105,f2230])).
% 4.81/1.00  fof(f2184,plain,(
% 4.81/1.00    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_66 | ~spl3_169)),
% 4.81/1.00    inference(subsumption_resolution,[],[f2183,f107])).
% 4.81/1.00  fof(f2183,plain,(
% 4.81/1.00    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_66 | ~spl3_169)),
% 4.81/1.00    inference(subsumption_resolution,[],[f2177,f771])).
% 4.81/1.00  fof(f2177,plain,(
% 4.81/1.00    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_169),
% 4.81/1.00    inference(superposition,[],[f89,f2003])).
% 4.81/1.00  fof(f89,plain,(
% 4.81/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f41])).
% 4.81/1.00  fof(f41,plain,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(flattening,[],[f40])).
% 4.81/1.00  fof(f40,plain,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.81/1.00    inference(ennf_transformation,[],[f14])).
% 4.81/1.00  fof(f14,axiom,(
% 4.81/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 4.81/1.00  fof(f2004,plain,(
% 4.81/1.00    spl3_169 | ~spl3_51 | ~spl3_66 | ~spl3_78),
% 4.81/1.00    inference(avatar_split_clause,[],[f1007,f943,f770,f585,f2001])).
% 4.81/1.00  fof(f943,plain,(
% 4.81/1.00    spl3_78 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 4.81/1.00  fof(f1007,plain,(
% 4.81/1.00    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl3_51 | ~spl3_66 | ~spl3_78)),
% 4.81/1.00    inference(forward_demodulation,[],[f1000,f587])).
% 4.81/1.00  fof(f1000,plain,(
% 4.81/1.00    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl3_66 | ~spl3_78)),
% 4.81/1.00    inference(resolution,[],[f944,f771])).
% 4.81/1.00  fof(f944,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0)))) ) | ~spl3_78),
% 4.81/1.00    inference(avatar_component_clause,[],[f943])).
% 4.81/1.00  fof(f1806,plain,(
% 4.81/1.00    ~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_133),
% 4.81/1.00    inference(avatar_contradiction_clause,[],[f1805])).
% 4.81/1.00  fof(f1805,plain,(
% 4.81/1.00    $false | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_133)),
% 4.81/1.00    inference(unit_resulting_resolution,[],[f107,f112,f1572,f116,f81])).
% 4.81/1.00  fof(f81,plain,(
% 4.81/1.00    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f62])).
% 4.81/1.00  fof(f62,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(nnf_transformation,[],[f33])).
% 4.81/1.00  fof(f33,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f23])).
% 4.81/1.00  fof(f23,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 4.81/1.00  fof(f116,plain,(
% 4.81/1.00    ~v2_tops_1(sK1,sK0) | spl3_3),
% 4.81/1.00    inference(avatar_component_clause,[],[f115])).
% 4.81/1.00  fof(f115,plain,(
% 4.81/1.00    spl3_3 <=> v2_tops_1(sK1,sK0)),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.81/1.00  fof(f1572,plain,(
% 4.81/1.00    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_133),
% 4.81/1.00    inference(avatar_component_clause,[],[f1570])).
% 4.81/1.00  fof(f1801,plain,(
% 4.81/1.00    spl3_147 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 4.81/1.00    inference(avatar_split_clause,[],[f1772,f115,f110,f105,f1798])).
% 4.81/1.00  fof(f1772,plain,(
% 4.81/1.00    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 4.81/1.00    inference(subsumption_resolution,[],[f1771,f107])).
% 4.81/1.00  fof(f1771,plain,(
% 4.81/1.00    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_3)),
% 4.81/1.00    inference(subsumption_resolution,[],[f1769,f112])).
% 4.81/1.00  fof(f1769,plain,(
% 4.81/1.00    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.81/1.00    inference(resolution,[],[f117,f82])).
% 4.81/1.00  fof(f82,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f63])).
% 4.81/1.00  fof(f63,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(nnf_transformation,[],[f34])).
% 4.81/1.00  fof(f34,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f17])).
% 4.81/1.00  fof(f17,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 4.81/1.00  fof(f117,plain,(
% 4.81/1.00    v2_tops_1(sK1,sK0) | ~spl3_3),
% 4.81/1.00    inference(avatar_component_clause,[],[f115])).
% 4.81/1.00  fof(f1725,plain,(
% 4.81/1.00    spl3_141 | ~spl3_57),
% 4.81/1.00    inference(avatar_split_clause,[],[f703,f644,f1723])).
% 4.81/1.00  fof(f644,plain,(
% 4.81/1.00    spl3_57 <=> ! [X5,X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X5,k1_tops_1(sK0,X4)) | ~sP2(k2_tops_1(sK0,X4),X5))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 4.81/1.00  fof(f703,plain,(
% 4.81/1.00    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~sP2(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1))) ) | ~spl3_57),
% 4.81/1.00    inference(resolution,[],[f645,f100])).
% 4.81/1.00  fof(f645,plain,(
% 4.81/1.00    ( ! [X4,X5] : (~r1_tarski(X5,k1_tops_1(sK0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~sP2(k2_tops_1(sK0,X4),X5)) ) | ~spl3_57),
% 4.81/1.00    inference(avatar_component_clause,[],[f644])).
% 4.81/1.00  fof(f1573,plain,(
% 4.81/1.00    spl3_133 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 4.81/1.00    inference(avatar_split_clause,[],[f1560,f115,f110,f105,f1570])).
% 4.81/1.00  fof(f1560,plain,(
% 4.81/1.00    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 4.81/1.00    inference(subsumption_resolution,[],[f1559,f107])).
% 4.81/1.00  fof(f1559,plain,(
% 4.81/1.00    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_3)),
% 4.81/1.00    inference(subsumption_resolution,[],[f1556,f112])).
% 4.81/1.00  fof(f1556,plain,(
% 4.81/1.00    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.81/1.00    inference(resolution,[],[f117,f80])).
% 4.81/1.00  fof(f80,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f62])).
% 4.81/1.00  fof(f1554,plain,(
% 4.81/1.00    spl3_132 | ~spl3_58),
% 4.81/1.00    inference(avatar_split_clause,[],[f696,f651,f1552])).
% 4.81/1.00  fof(f651,plain,(
% 4.81/1.00    spl3_58 <=> r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 4.81/1.00  fof(f696,plain,(
% 4.81/1.00    ( ! [X2] : (~r1_tarski(X2,sK1) | ~sP2(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2)) ) | ~spl3_58),
% 4.81/1.00    inference(resolution,[],[f653,f103])).
% 4.81/1.00  fof(f103,plain,(
% 4.81/1.00    ( ! [X0,X3,X1] : (~r1_xboole_0(X1,X3) | ~r1_tarski(X0,X1) | ~sP2(X3,X0)) )),
% 4.81/1.00    inference(general_splitting,[],[f99,f102_D])).
% 4.81/1.00  fof(f99,plain,(
% 4.81/1.00    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f55])).
% 4.81/1.00  fof(f55,plain,(
% 4.81/1.00    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 4.81/1.00    inference(flattening,[],[f54])).
% 4.81/1.00  fof(f54,plain,(
% 4.81/1.00    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 4.81/1.00    inference(ennf_transformation,[],[f3])).
% 4.81/1.00  fof(f3,axiom,(
% 4.81/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).
% 4.81/1.00  fof(f653,plain,(
% 4.81/1.00    r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl3_58),
% 4.81/1.00    inference(avatar_component_clause,[],[f651])).
% 4.81/1.00  fof(f1532,plain,(
% 4.81/1.00    spl3_128 | ~spl3_27),
% 4.81/1.00    inference(avatar_split_clause,[],[f398,f384,f1530])).
% 4.81/1.00  fof(f384,plain,(
% 4.81/1.00    spl3_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 4.81/1.00  fof(f398,plain,(
% 4.81/1.00    ( ! [X0] : (k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_27),
% 4.81/1.00    inference(resolution,[],[f385,f84])).
% 4.81/1.00  fof(f385,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl3_27),
% 4.81/1.00    inference(avatar_component_clause,[],[f384])).
% 4.81/1.00  fof(f1505,plain,(
% 4.81/1.00    spl3_123 | ~spl3_16),
% 4.81/1.00    inference(avatar_split_clause,[],[f288,f266,f1503])).
% 4.81/1.00  fof(f266,plain,(
% 4.81/1.00    spl3_16 <=> r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 4.81/1.00  fof(f288,plain,(
% 4.81/1.00    ( ! [X1] : (r1_tarski(sK1,X1) | ~r1_tarski(sK1,k2_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)))) ) | ~spl3_16),
% 4.81/1.00    inference(resolution,[],[f268,f98])).
% 4.81/1.00  fof(f98,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f53])).
% 4.81/1.00  fof(f53,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.81/1.00    inference(flattening,[],[f52])).
% 4.81/1.00  fof(f52,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 4.81/1.00    inference(ennf_transformation,[],[f5])).
% 4.81/1.00  fof(f5,axiom,(
% 4.81/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 4.81/1.00  fof(f268,plain,(
% 4.81/1.00    r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_16),
% 4.81/1.00    inference(avatar_component_clause,[],[f266])).
% 4.81/1.00  fof(f1437,plain,(
% 4.81/1.00    spl3_119 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f461,f105,f1435])).
% 4.81/1.00  fof(f461,plain,(
% 4.81/1.00    ( ! [X0,X1] : (k2_xboole_0(k2_tops_1(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f215,f107])).
% 4.81/1.00  fof(f215,plain,(
% 4.81/1.00    ( ! [X10,X8,X9] : (~l1_pre_topc(X9) | k2_xboole_0(k2_tops_1(X9,X10),X8) = k4_subset_1(u1_struct_0(X9),k2_tops_1(X9,X10),X8) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))) )),
% 4.81/1.00    inference(resolution,[],[f96,f90])).
% 4.81/1.00  fof(f90,plain,(
% 4.81/1.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f43])).
% 4.81/1.00  fof(f43,plain,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(flattening,[],[f42])).
% 4.81/1.00  fof(f42,plain,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.81/1.00    inference(ennf_transformation,[],[f18])).
% 4.81/1.00  fof(f18,axiom,(
% 4.81/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 4.81/1.00  fof(f96,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f49])).
% 4.81/1.00  fof(f49,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(flattening,[],[f48])).
% 4.81/1.00  fof(f48,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.81/1.00    inference(ennf_transformation,[],[f9])).
% 4.81/1.00  fof(f9,axiom,(
% 4.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.81/1.00  fof(f1317,plain,(
% 4.81/1.00    spl3_112 | ~spl3_2),
% 4.81/1.00    inference(avatar_split_clause,[],[f459,f110,f1315])).
% 4.81/1.00  fof(f459,plain,(
% 4.81/1.00    ( ! [X11] : (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X11) = k4_subset_1(u1_struct_0(sK0),X11,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 4.81/1.00    inference(resolution,[],[f228,f112])).
% 4.81/1.00  fof(f228,plain,(
% 4.81/1.00    ( ! [X4,X2,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | k4_subset_1(X3,k3_subset_1(X3,X4),X2) = k4_subset_1(X3,X2,k3_subset_1(X3,X4)) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 4.81/1.00    inference(resolution,[],[f97,f84])).
% 4.81/1.00  fof(f97,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f51])).
% 4.81/1.00  fof(f51,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(flattening,[],[f50])).
% 4.81/1.00  fof(f50,plain,(
% 4.81/1.00    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.81/1.00    inference(ennf_transformation,[],[f6])).
% 4.81/1.00  fof(f6,axiom,(
% 4.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 4.81/1.00  fof(f945,plain,(
% 4.81/1.00    spl3_78 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f438,f105,f943])).
% 4.81/1.00  fof(f438,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0)))) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f158,f107])).
% 4.81/1.00  fof(f158,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 4.81/1.00    inference(resolution,[],[f89,f85])).
% 4.81/1.00  fof(f85,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 4.81/1.00    inference(cnf_transformation,[],[f36])).
% 4.81/1.00  fof(f36,plain,(
% 4.81/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.81/1.00    inference(ennf_transformation,[],[f8])).
% 4.81/1.00  fof(f8,axiom,(
% 4.81/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 4.81/1.00  fof(f782,plain,(
% 4.81/1.00    ~spl3_2 | spl3_66),
% 4.81/1.00    inference(avatar_contradiction_clause,[],[f781])).
% 4.81/1.00  fof(f781,plain,(
% 4.81/1.00    $false | (~spl3_2 | spl3_66)),
% 4.81/1.00    inference(subsumption_resolution,[],[f779,f112])).
% 4.81/1.00  fof(f779,plain,(
% 4.81/1.00    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_66),
% 4.81/1.00    inference(resolution,[],[f772,f84])).
% 4.81/1.00  fof(f772,plain,(
% 4.81/1.00    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_66),
% 4.81/1.00    inference(avatar_component_clause,[],[f770])).
% 4.81/1.00  fof(f664,plain,(
% 4.81/1.00    ~spl3_1 | ~spl3_2 | spl3_59),
% 4.81/1.00    inference(avatar_contradiction_clause,[],[f663])).
% 4.81/1.00  fof(f663,plain,(
% 4.81/1.00    $false | (~spl3_1 | ~spl3_2 | spl3_59)),
% 4.81/1.00    inference(subsumption_resolution,[],[f662,f107])).
% 4.81/1.00  fof(f662,plain,(
% 4.81/1.00    ~l1_pre_topc(sK0) | (~spl3_2 | spl3_59)),
% 4.81/1.00    inference(subsumption_resolution,[],[f660,f112])).
% 4.81/1.00  fof(f660,plain,(
% 4.81/1.00    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_59),
% 4.81/1.00    inference(resolution,[],[f657,f90])).
% 4.81/1.00  fof(f657,plain,(
% 4.81/1.00    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_59),
% 4.81/1.00    inference(avatar_component_clause,[],[f655])).
% 4.81/1.00  fof(f658,plain,(
% 4.81/1.00    spl3_58 | ~spl3_59 | ~spl3_2 | ~spl3_29),
% 4.81/1.00    inference(avatar_split_clause,[],[f414,f409,f110,f655,f651])).
% 4.81/1.00  fof(f409,plain,(
% 4.81/1.00    spl3_29 <=> ! [X4] : (r1_xboole_0(sK1,k3_subset_1(X4,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X4)) | ~m1_subset_1(sK1,k1_zfmisc_1(X4)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 4.81/1.00  fof(f414,plain,(
% 4.81/1.00    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl3_2 | ~spl3_29)),
% 4.81/1.00    inference(resolution,[],[f410,f112])).
% 4.81/1.00  fof(f410,plain,(
% 4.81/1.00    ( ! [X4] : (~m1_subset_1(sK1,k1_zfmisc_1(X4)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X4)) | r1_xboole_0(sK1,k3_subset_1(X4,k2_tops_1(sK0,sK1)))) ) | ~spl3_29),
% 4.81/1.00    inference(avatar_component_clause,[],[f409])).
% 4.81/1.00  fof(f646,plain,(
% 4.81/1.00    spl3_57 | ~spl3_18),
% 4.81/1.00    inference(avatar_split_clause,[],[f301,f292,f644])).
% 4.81/1.00  fof(f292,plain,(
% 4.81/1.00    spl3_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 4.81/1.00  fof(f301,plain,(
% 4.81/1.00    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X5,k1_tops_1(sK0,X4)) | ~sP2(k2_tops_1(sK0,X4),X5)) ) | ~spl3_18),
% 4.81/1.00    inference(resolution,[],[f293,f103])).
% 4.81/1.00  fof(f293,plain,(
% 4.81/1.00    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 4.81/1.00    inference(avatar_component_clause,[],[f292])).
% 4.81/1.00  fof(f588,plain,(
% 4.81/1.00    spl3_51 | ~spl3_2 | ~spl3_31),
% 4.81/1.00    inference(avatar_split_clause,[],[f429,f420,f110,f585])).
% 4.81/1.00  fof(f420,plain,(
% 4.81/1.00    spl3_31 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 4.81/1.00  fof(f429,plain,(
% 4.81/1.00    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_2 | ~spl3_31)),
% 4.81/1.00    inference(resolution,[],[f421,f112])).
% 4.81/1.00  fof(f421,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl3_31),
% 4.81/1.00    inference(avatar_component_clause,[],[f420])).
% 4.81/1.00  fof(f487,plain,(
% 4.81/1.00    spl3_39 | ~spl3_2 | ~spl3_23),
% 4.81/1.00    inference(avatar_split_clause,[],[f361,f354,f110,f484])).
% 4.81/1.00  fof(f354,plain,(
% 4.81/1.00    spl3_23 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 4.81/1.00  fof(f361,plain,(
% 4.81/1.00    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_23)),
% 4.81/1.00    inference(resolution,[],[f355,f112])).
% 4.81/1.00  fof(f355,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) | ~spl3_23),
% 4.81/1.00    inference(avatar_component_clause,[],[f354])).
% 4.81/1.00  fof(f422,plain,(
% 4.81/1.00    spl3_31 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f246,f105,f420])).
% 4.81/1.00  fof(f246,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f77,f107])).
% 4.81/1.00  fof(f77,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f31])).
% 4.81/1.00  fof(f31,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f15])).
% 4.81/1.00  fof(f15,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 4.81/1.00  fof(f411,plain,(
% 4.81/1.00    spl3_29 | ~spl3_4),
% 4.81/1.00    inference(avatar_split_clause,[],[f203,f119,f409])).
% 4.81/1.00  fof(f203,plain,(
% 4.81/1.00    ( ! [X4] : (r1_xboole_0(sK1,k3_subset_1(X4,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X4)) | ~m1_subset_1(sK1,k1_zfmisc_1(X4))) ) | ~spl3_4),
% 4.81/1.00    inference(resolution,[],[f88,f121])).
% 4.81/1.00  fof(f121,plain,(
% 4.81/1.00    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl3_4),
% 4.81/1.00    inference(avatar_component_clause,[],[f119])).
% 4.81/1.00  fof(f88,plain,(
% 4.81/1.00    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f64])).
% 4.81/1.00  fof(f386,plain,(
% 4.81/1.00    spl3_27 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f234,f105,f384])).
% 4.81/1.00  fof(f234,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f76,f107])).
% 4.81/1.00  fof(f76,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f30])).
% 4.81/1.00  fof(f30,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f21])).
% 4.81/1.00  fof(f21,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 4.81/1.00  fof(f356,plain,(
% 4.81/1.00    spl3_23 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f221,f105,f354])).
% 4.81/1.00  fof(f221,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f75,f107])).
% 4.81/1.00  fof(f75,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f29])).
% 4.81/1.00  fof(f29,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f20])).
% 4.81/1.00  fof(f20,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 4.81/1.00  fof(f294,plain,(
% 4.81/1.00    spl3_18 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f157,f105,f292])).
% 4.81/1.00  fof(f157,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0))) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f74,f107])).
% 4.81/1.00  fof(f74,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))) )),
% 4.81/1.00    inference(cnf_transformation,[],[f28])).
% 4.81/1.00  fof(f28,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f22])).
% 4.81/1.00  fof(f22,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).
% 4.81/1.00  fof(f269,plain,(
% 4.81/1.00    spl3_16 | ~spl3_2),
% 4.81/1.00    inference(avatar_split_clause,[],[f254,f110,f266])).
% 4.81/1.00  fof(f254,plain,(
% 4.81/1.00    r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_2),
% 4.81/1.00    inference(resolution,[],[f205,f112])).
% 4.81/1.00  fof(f205,plain,(
% 4.81/1.00    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | r1_xboole_0(X2,k3_subset_1(X3,X2))) )),
% 4.81/1.00    inference(duplicate_literal_removal,[],[f202])).
% 4.81/1.00  fof(f202,plain,(
% 4.81/1.00    ( ! [X2,X3] : (r1_xboole_0(X2,k3_subset_1(X3,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 4.81/1.00    inference(resolution,[],[f88,f100])).
% 4.81/1.00  fof(f180,plain,(
% 4.81/1.00    spl3_11 | ~spl3_2 | ~spl3_9),
% 4.81/1.00    inference(avatar_split_clause,[],[f168,f160,f110,f177])).
% 4.81/1.00  fof(f160,plain,(
% 4.81/1.00    spl3_9 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 4.81/1.00    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 4.81/1.00  fof(f168,plain,(
% 4.81/1.00    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 4.81/1.00    inference(resolution,[],[f161,f112])).
% 4.81/1.00  fof(f161,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl3_9),
% 4.81/1.00    inference(avatar_component_clause,[],[f160])).
% 4.81/1.00  fof(f162,plain,(
% 4.81/1.00    spl3_9 | ~spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f146,f105,f160])).
% 4.81/1.00  fof(f146,plain,(
% 4.81/1.00    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl3_1),
% 4.81/1.00    inference(resolution,[],[f73,f107])).
% 4.81/1.00  fof(f73,plain,(
% 4.81/1.00    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 4.81/1.00    inference(cnf_transformation,[],[f27])).
% 4.81/1.00  fof(f27,plain,(
% 4.81/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f19])).
% 4.81/1.00  fof(f19,axiom,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 4.81/1.00  fof(f124,plain,(
% 4.81/1.00    ~spl3_3 | ~spl3_4),
% 4.81/1.00    inference(avatar_split_clause,[],[f123,f119,f115])).
% 4.81/1.00  fof(f123,plain,(
% 4.81/1.00    ~v2_tops_1(sK1,sK0) | ~spl3_4),
% 4.81/1.00    inference(subsumption_resolution,[],[f70,f121])).
% 4.81/1.00  fof(f70,plain,(
% 4.81/1.00    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 4.81/1.00    inference(cnf_transformation,[],[f60])).
% 4.81/1.00  fof(f60,plain,(
% 4.81/1.00    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 4.81/1.00  fof(f58,plain,(
% 4.81/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.81/1.00    introduced(choice_axiom,[])).
% 4.81/1.00  fof(f59,plain,(
% 4.81/1.00    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.81/1.00    introduced(choice_axiom,[])).
% 4.81/1.00  fof(f57,plain,(
% 4.81/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.81/1.00    inference(flattening,[],[f56])).
% 4.81/1.00  fof(f56,plain,(
% 4.81/1.00    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.81/1.00    inference(nnf_transformation,[],[f26])).
% 4.81/1.00  fof(f26,plain,(
% 4.81/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.81/1.00    inference(ennf_transformation,[],[f25])).
% 4.81/1.00  fof(f25,negated_conjecture,(
% 4.81/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 4.81/1.00    inference(negated_conjecture,[],[f24])).
% 4.81/1.00  fof(f24,conjecture,(
% 4.81/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 4.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 4.81/1.00  fof(f122,plain,(
% 4.81/1.00    spl3_3 | spl3_4),
% 4.81/1.00    inference(avatar_split_clause,[],[f69,f119,f115])).
% 4.81/1.00  fof(f69,plain,(
% 4.81/1.00    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 4.81/1.00    inference(cnf_transformation,[],[f60])).
% 4.81/1.00  fof(f113,plain,(
% 4.81/1.00    spl3_2),
% 4.81/1.00    inference(avatar_split_clause,[],[f68,f110])).
% 4.81/1.00  fof(f68,plain,(
% 4.81/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.81/1.00    inference(cnf_transformation,[],[f60])).
% 4.81/1.00  fof(f108,plain,(
% 4.81/1.00    spl3_1),
% 4.81/1.00    inference(avatar_split_clause,[],[f67,f105])).
% 4.81/1.00  fof(f67,plain,(
% 4.81/1.00    l1_pre_topc(sK0)),
% 4.81/1.00    inference(cnf_transformation,[],[f60])).
% 4.81/1.00  % SZS output end Proof for theBenchmark
% 4.81/1.00  % (20952)------------------------------
% 4.81/1.00  % (20952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.00  % (20952)Termination reason: Refutation
% 4.81/1.00  
% 4.81/1.00  % (20952)Memory used [KB]: 9722
% 4.81/1.00  % (20952)Time elapsed: 0.560 s
% 4.81/1.00  % (20952)------------------------------
% 4.81/1.00  % (20952)------------------------------
% 4.81/1.00  % (20949)Success in time 0.637 s
%------------------------------------------------------------------------------
