%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 280 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :    8
%              Number of atoms          :  346 ( 717 expanded)
%              Number of equality atoms :   59 ( 150 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1012,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f95,f96,f97,f145,f150,f190,f253,f353,f354,f402,f703,f708,f758,f814,f820,f829,f865,f905,f994,f1004])).

fof(f1004,plain,
    ( ~ spl3_16
    | spl3_86
    | ~ spl3_94 ),
    inference(avatar_contradiction_clause,[],[f1003])).

fof(f1003,plain,
    ( $false
    | ~ spl3_16
    | spl3_86
    | ~ spl3_94 ),
    inference(subsumption_resolution,[],[f1002,f904])).

fof(f904,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f902])).

fof(f902,plain,
    ( spl3_94
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

% (12083)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f1002,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_16
    | spl3_86 ),
    inference(forward_demodulation,[],[f1001,f73])).

fof(f73,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f52,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f1001,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | ~ spl3_16
    | spl3_86 ),
    inference(forward_demodulation,[],[f864,f169])).

fof(f169,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f864,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_86 ),
    inference(avatar_component_clause,[],[f862])).

fof(f862,plain,
    ( spl3_86
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f994,plain,
    ( ~ spl3_16
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl3_16
    | spl3_37 ),
    inference(subsumption_resolution,[],[f992,f753])).

fof(f753,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f749,f73])).

fof(f749,plain,(
    ! [X0] : m1_subset_1(k8_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f992,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_16
    | spl3_37 ),
    inference(forward_demodulation,[],[f991,f73])).

fof(f991,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | ~ spl3_16
    | spl3_37 ),
    inference(forward_demodulation,[],[f601,f169])).

fof(f601,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f401,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f401,plain,
    ( ~ r1_tarski(sK0,k8_setfam_1(sK0,sK1))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl3_37
  <=> r1_tarski(sK0,k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f905,plain,
    ( spl3_94
    | ~ spl3_77
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f855,f811,f755,f902])).

fof(f755,plain,
    ( spl3_77
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f811,plain,
    ( spl3_83
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f855,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_77
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f757,f813])).

fof(f813,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f811])).

fof(f757,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f755])).

fof(f865,plain,
    ( ~ spl3_86
    | spl3_7
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f844,f811,f92,f862])).

fof(f92,plain,
    ( spl3_7
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f844,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_7
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f94,f813])).

fof(f94,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f829,plain,
    ( k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2)
    | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1)
    | ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f820,plain,
    ( spl3_84
    | ~ spl3_4
    | spl3_16
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f815,f705,f167,f69,f817])).

fof(f817,plain,
    ( spl3_84
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f69,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f705,plain,
    ( spl3_73
  <=> k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f815,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_4
    | spl3_16
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f803,f707])).

fof(f707,plain,
    ( k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f705])).

fof(f803,plain,
    ( k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_4
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f168,f71,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f168,plain,
    ( k1_xboole_0 != sK1
    | spl3_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f814,plain,
    ( spl3_83
    | ~ spl3_3
    | spl3_18
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f809,f700,f186,f64,f811])).

fof(f64,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f186,plain,
    ( spl3_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f700,plain,
    ( spl3_72
  <=> k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f809,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3
    | spl3_18
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f804,f702])).

fof(f702,plain,
    ( k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f700])).

fof(f804,plain,
    ( k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_3
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f187,f66,f41])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f187,plain,
    ( k1_xboole_0 != sK2
    | spl3_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f758,plain,
    ( spl3_77
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f748,f64,f755])).

fof(f748,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f40])).

fof(f708,plain,
    ( spl3_73
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f696,f69,f705])).

fof(f696,plain,
    ( k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f703,plain,
    ( spl3_72
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f697,f64,f700])).

fof(f697,plain,
    ( k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f39])).

fof(f402,plain,
    ( ~ spl3_37
    | spl3_1
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f397,f186,f54,f399])).

fof(f54,plain,
    ( spl3_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f397,plain,
    ( ~ r1_tarski(sK0,k8_setfam_1(sK0,sK1))
    | spl3_1
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f360,f73])).

fof(f360,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1))
    | spl3_1
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f56,f188])).

fof(f188,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f56,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f354,plain,
    ( ~ spl3_17
    | ~ spl3_2
    | spl3_25 ),
    inference(avatar_split_clause,[],[f254,f248,f59,f182])).

fof(f182,plain,
    ( spl3_17
  <=> r1_xboole_0(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f59,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f248,plain,
    ( spl3_25
  <=> r1_xboole_0(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f254,plain,
    ( ~ r1_xboole_0(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f61,f250,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f250,plain,
    ( ~ r1_xboole_0(sK1,k1_zfmisc_1(sK0))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f248])).

fof(f61,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f353,plain,
    ( spl3_35
    | ~ spl3_2
    | spl3_16 ),
    inference(avatar_split_clause,[],[f336,f167,f59,f350])).

fof(f350,plain,
    ( spl3_35
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f336,plain,
    ( r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_2
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f61,f168,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f253,plain,
    ( ~ spl3_25
    | ~ spl3_13
    | spl3_16 ),
    inference(avatar_split_clause,[],[f252,f167,f147,f248])).

fof(f147,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f252,plain,
    ( ~ r1_xboole_0(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_13
    | spl3_16 ),
    inference(subsumption_resolution,[],[f244,f168])).

fof(f244,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_xboole_0(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(superposition,[],[f43,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f190,plain,
    ( spl3_17
    | ~ spl3_18
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f178,f142,f186,f182])).

fof(f142,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f178,plain,
    ( k1_xboole_0 != sK2
    | r1_xboole_0(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_12 ),
    inference(superposition,[],[f44,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f150,plain,
    ( spl3_13
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f131,f82,f147])).

fof(f82,plain,
    ( spl3_5
  <=> r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f131,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f84,f48])).

% (12085)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f84,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f145,plain,
    ( spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f87,f142])).

fof(f87,plain,
    ( spl3_6
  <=> r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f132,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f89,f48])).

fof(f89,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f97,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f79,f69,f82])).

fof(f79,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f45,f71])).

fof(f96,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f78,f64,f87])).

fof(f78,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f45,f66])).

fof(f95,plain,
    ( ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f74,f54,f92])).

fof(f74,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f45])).

fof(f72,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f67,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f54])).

fof(f36,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (12086)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (12080)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (12088)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (12088)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1012,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f95,f96,f97,f145,f150,f190,f253,f353,f354,f402,f703,f708,f758,f814,f820,f829,f865,f905,f994,f1004])).
% 0.21/0.51  fof(f1004,plain,(
% 0.21/0.51    ~spl3_16 | spl3_86 | ~spl3_94),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1003])).
% 0.21/0.51  fof(f1003,plain,(
% 0.21/0.51    $false | (~spl3_16 | spl3_86 | ~spl3_94)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1002,f904])).
% 0.21/0.51  fof(f904,plain,(
% 0.21/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_94),
% 0.21/0.51    inference(avatar_component_clause,[],[f902])).
% 0.21/0.51  fof(f902,plain,(
% 0.21/0.51    spl3_94 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 0.21/0.51  % (12083)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  fof(f1002,plain,(
% 0.21/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_16 | spl3_86)),
% 0.21/0.51    inference(forward_demodulation,[],[f1001,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.51  fof(f1001,plain,(
% 0.21/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (~spl3_16 | spl3_86)),
% 0.21/0.51    inference(forward_demodulation,[],[f864,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl3_16 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.51  fof(f864,plain,(
% 0.21/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_86),
% 0.21/0.51    inference(avatar_component_clause,[],[f862])).
% 0.21/0.51  fof(f862,plain,(
% 0.21/0.51    spl3_86 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 0.21/0.51  fof(f994,plain,(
% 0.21/0.51    ~spl3_16 | spl3_37),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f993])).
% 0.21/0.51  fof(f993,plain,(
% 0.21/0.51    $false | (~spl3_16 | spl3_37)),
% 0.21/0.51    inference(subsumption_resolution,[],[f992,f753])).
% 0.21/0.51  fof(f753,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f749,f73])).
% 0.21/0.51  fof(f749,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k8_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f37,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.51  fof(f992,plain,(
% 0.21/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | (~spl3_16 | spl3_37)),
% 0.21/0.51    inference(forward_demodulation,[],[f991,f73])).
% 0.21/0.51  fof(f991,plain,(
% 0.21/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (~spl3_16 | spl3_37)),
% 0.21/0.51    inference(forward_demodulation,[],[f601,f169])).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_37),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f401,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    ~r1_tarski(sK0,k8_setfam_1(sK0,sK1)) | spl3_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f399])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    spl3_37 <=> r1_tarski(sK0,k8_setfam_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.51  fof(f905,plain,(
% 0.21/0.51    spl3_94 | ~spl3_77 | ~spl3_83),
% 0.21/0.51    inference(avatar_split_clause,[],[f855,f811,f755,f902])).
% 0.21/0.51  fof(f755,plain,(
% 0.21/0.51    spl3_77 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.21/0.51  fof(f811,plain,(
% 0.21/0.51    spl3_83 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.21/0.51  fof(f855,plain,(
% 0.21/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_77 | ~spl3_83)),
% 0.21/0.51    inference(backward_demodulation,[],[f757,f813])).
% 0.21/0.51  fof(f813,plain,(
% 0.21/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_83),
% 0.21/0.51    inference(avatar_component_clause,[],[f811])).
% 0.21/0.51  fof(f757,plain,(
% 0.21/0.51    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_77),
% 0.21/0.51    inference(avatar_component_clause,[],[f755])).
% 0.21/0.51  fof(f865,plain,(
% 0.21/0.51    ~spl3_86 | spl3_7 | ~spl3_83),
% 0.21/0.51    inference(avatar_split_clause,[],[f844,f811,f92,f862])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl3_7 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f844,plain,(
% 0.21/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | (spl3_7 | ~spl3_83)),
% 0.21/0.51    inference(backward_demodulation,[],[f94,f813])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f829,plain,(
% 0.21/0.51    k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2) | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1) | ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f820,plain,(
% 0.21/0.51    spl3_84 | ~spl3_4 | spl3_16 | ~spl3_73),
% 0.21/0.51    inference(avatar_split_clause,[],[f815,f705,f167,f69,f817])).
% 0.21/0.51  fof(f817,plain,(
% 0.21/0.51    spl3_84 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f705,plain,(
% 0.21/0.51    spl3_73 <=> k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.51  fof(f815,plain,(
% 0.21/0.51    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | (~spl3_4 | spl3_16 | ~spl3_73)),
% 0.21/0.51    inference(forward_demodulation,[],[f803,f707])).
% 0.21/0.51  fof(f707,plain,(
% 0.21/0.51    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) | ~spl3_73),
% 0.21/0.51    inference(avatar_component_clause,[],[f705])).
% 0.21/0.51  fof(f803,plain,(
% 0.21/0.51    k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | (~spl3_4 | spl3_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f168,f71,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f167])).
% 0.21/0.51  fof(f814,plain,(
% 0.21/0.51    spl3_83 | ~spl3_3 | spl3_18 | ~spl3_72),
% 0.21/0.51    inference(avatar_split_clause,[],[f809,f700,f186,f64,f811])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    spl3_18 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.51  fof(f700,plain,(
% 0.21/0.51    spl3_72 <=> k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.51  fof(f809,plain,(
% 0.21/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl3_3 | spl3_18 | ~spl3_72)),
% 0.21/0.51    inference(forward_demodulation,[],[f804,f702])).
% 0.21/0.51  fof(f702,plain,(
% 0.21/0.51    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) | ~spl3_72),
% 0.21/0.51    inference(avatar_component_clause,[],[f700])).
% 0.21/0.51  fof(f804,plain,(
% 0.21/0.51    k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | (~spl3_3 | spl3_18)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f187,f66,f41])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | spl3_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f186])).
% 0.21/0.51  fof(f758,plain,(
% 0.21/0.51    spl3_77 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f748,f64,f755])).
% 0.21/0.51  fof(f748,plain,(
% 0.21/0.51    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f66,f40])).
% 0.21/0.51  fof(f708,plain,(
% 0.21/0.51    spl3_73 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f696,f69,f705])).
% 0.21/0.51  fof(f696,plain,(
% 0.21/0.51    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) | ~spl3_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f71,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.51  fof(f703,plain,(
% 0.21/0.51    spl3_72 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f697,f64,f700])).
% 0.21/0.51  fof(f697,plain,(
% 0.21/0.51    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) | ~spl3_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f66,f39])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    ~spl3_37 | spl3_1 | ~spl3_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f397,f186,f54,f399])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    ~r1_tarski(sK0,k8_setfam_1(sK0,sK1)) | (spl3_1 | ~spl3_18)),
% 0.21/0.51    inference(forward_demodulation,[],[f360,f73])).
% 0.21/0.51  fof(f360,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) | (spl3_1 | ~spl3_18)),
% 0.21/0.51    inference(backward_demodulation,[],[f56,f188])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl3_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f186])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    ~spl3_17 | ~spl3_2 | spl3_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f254,f248,f59,f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl3_17 <=> r1_xboole_0(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    spl3_25 <=> r1_xboole_0(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ~r1_xboole_0(sK2,k1_zfmisc_1(sK0)) | (~spl3_2 | spl3_25)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f61,f250,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    ~r1_xboole_0(sK1,k1_zfmisc_1(sK0)) | spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f248])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    spl3_35 | ~spl3_2 | spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f336,f167,f59,f350])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    spl3_35 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl3_2 | spl3_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f61,f168,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~spl3_25 | ~spl3_13 | spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f252,f167,f147,f248])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ~r1_xboole_0(sK1,k1_zfmisc_1(sK0)) | (~spl3_13 | spl3_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f244,f168])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~r1_xboole_0(sK1,k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.21/0.51    inference(superposition,[],[f43,f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    spl3_17 | ~spl3_18 | ~spl3_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f178,f142,f186,f182])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl3_12 <=> k1_xboole_0 = k4_xboole_0(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | r1_xboole_0(sK2,k1_zfmisc_1(sK0)) | ~spl3_12),
% 0.21/0.51    inference(superposition,[],[f44,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK2,k1_zfmisc_1(sK0)) | ~spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl3_13 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f131,f82,f147])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl3_5 <=> r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f84,f48])).
% 0.21/0.51  % (12085)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    r1_tarski(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl3_12 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f132,f87,f142])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl3_6 <=> r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK2,k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f89,f48])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl3_5 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f69,f82])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    r1_tarski(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f45,f71])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl3_6 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f78,f64,f87])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f45,f66])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~spl3_7 | spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f74,f54,f92])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f56,f45])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f69])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f64])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f59])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f54])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12088)------------------------------
% 0.21/0.51  % (12088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12088)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12088)Memory used [KB]: 11257
% 0.21/0.51  % (12088)Time elapsed: 0.085 s
% 0.21/0.51  % (12088)------------------------------
% 0.21/0.51  % (12088)------------------------------
% 0.21/0.51  % (12083)Refutation not found, incomplete strategy% (12083)------------------------------
% 0.21/0.51  % (12083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12071)Success in time 0.149 s
%------------------------------------------------------------------------------
