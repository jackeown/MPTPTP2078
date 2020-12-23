%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:36 EST 2020

% Result     : Theorem 4.49s
% Output     : Refutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 384 expanded)
%              Number of leaves         :   45 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  624 (1201 expanded)
%              Number of equality atoms :   96 ( 220 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f122,f127,f132,f137,f145,f256,f668,f1921,f2337,f2389,f2416,f2523,f2528,f2534,f2555,f2571,f2577,f2582,f2764,f3741,f3769])).

fof(f3769,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_77
    | ~ spl3_131 ),
    inference(avatar_contradiction_clause,[],[f3768])).

fof(f3768,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_77
    | ~ spl3_131 ),
    inference(subsumption_resolution,[],[f3767,f131])).

fof(f131,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f3767,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_77
    | ~ spl3_131 ),
    inference(subsumption_resolution,[],[f3766,f126])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f3766,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_77
    | ~ spl3_131 ),
    inference(subsumption_resolution,[],[f3749,f2351])).

fof(f2351,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl3_77 ),
    inference(avatar_component_clause,[],[f2350])).

fof(f2350,plain,
    ( spl3_77
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f3749,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_131 ),
    inference(superposition,[],[f269,f3740])).

fof(f3740,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_131 ),
    inference(avatar_component_clause,[],[f3738])).

fof(f3738,plain,
    ( spl3_131
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).

fof(f269,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f76,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3741,plain,
    ( spl3_86
    | spl3_131
    | ~ spl3_66
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f3736,f1907,f1876,f3738,f2625])).

fof(f2625,plain,
    ( spl3_86
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f1876,plain,
    ( spl3_66
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f1907,plain,
    ( spl3_72
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f3736,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_66
    | ~ spl3_72 ),
    inference(subsumption_resolution,[],[f3716,f1878])).

fof(f1878,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1876])).

fof(f3716,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_72 ),
    inference(superposition,[],[f787,f1909])).

fof(f1909,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f787,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f782,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f782,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f296,f76])).

fof(f296,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f292,f93])).

fof(f292,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f85,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f2764,plain,(
    ~ spl3_86 ),
    inference(avatar_contradiction_clause,[],[f2729])).

fof(f2729,plain,
    ( $false
    | ~ spl3_86 ),
    inference(unit_resulting_resolution,[],[f149,f94,f2626,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f2626,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f2625])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f149,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f147,f98])).

fof(f98,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f147,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f109,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f109,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f2582,plain,
    ( ~ spl3_76
    | spl3_77
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f2581,f401,f2350,f2346])).

fof(f2346,plain,
    ( spl3_76
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f401,plain,
    ( spl3_18
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f2581,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_18 ),
    inference(resolution,[],[f402,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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

fof(f402,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f401])).

fof(f2577,plain,
    ( spl3_71
    | ~ spl3_79 ),
    inference(avatar_contradiction_clause,[],[f2576])).

fof(f2576,plain,
    ( $false
    | spl3_71
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f2574,f2415])).

fof(f2415,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f2413])).

fof(f2413,plain,
    ( spl3_79
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f2574,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_71 ),
    inference(resolution,[],[f1905,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1905,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_71 ),
    inference(avatar_component_clause,[],[f1903])).

fof(f1903,plain,
    ( spl3_71
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f2571,plain,
    ( ~ spl3_71
    | spl3_72
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2549,f222,f1907,f1903])).

fof(f222,plain,
    ( spl3_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f2549,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f212,f224])).

fof(f224,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f222])).

fof(f212,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f80,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2555,plain,
    ( spl3_66
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2543,f222,f1876])).

fof(f2543,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f147,f224])).

fof(f2534,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f2533,f218,f118,f222])).

fof(f118,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f218,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f2533,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f2530,f219])).

fof(f219,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f218])).

fof(f2530,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f76,f119])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f2528,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2523,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_77 ),
    inference(avatar_contradiction_clause,[],[f2522])).

fof(f2522,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f2521,f131])).

fof(f2521,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f2520,f126])).

fof(f2520,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f2517,f223])).

fof(f223,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f222])).

fof(f2517,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_77 ),
    inference(superposition,[],[f924,f2352])).

fof(f2352,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f2350])).

fof(f924,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f298,f289])).

fof(f289,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f282,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f282,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f107,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f298,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f86,f76])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2416,plain,
    ( spl3_79
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2411,f129,f124,f2413])).

fof(f2411,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2401,f131])).

fof(f2401,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f715,f126])).

fof(f715,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(X3,k2_pre_topc(X4,X3))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f101,f287])).

fof(f287,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f284,f88])).

fof(f284,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f87,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2389,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(avatar_contradiction_clause,[],[f2388])).

fof(f2388,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(subsumption_resolution,[],[f2387,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2387,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(subsumption_resolution,[],[f2379,f115])).

fof(f115,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2379,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(resolution,[],[f2348,f329])).

fof(f329,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f321,f186])).

fof(f186,plain,
    ( ! [X15] :
        ( r1_tarski(X15,u1_struct_0(sK0))
        | ~ r1_tarski(X15,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f99,f144])).

fof(f144,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f321,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f315,f92])).

fof(f315,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X18,sK0)
        | r1_tarski(X18,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X18,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f311,f131])).

fof(f311,plain,
    ( ! [X18] :
        ( ~ r1_tarski(X18,sK1)
        | ~ v3_pre_topc(X18,sK0)
        | r1_tarski(X18,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f90,f126])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f2348,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_76 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f2337,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2336,f129,f124,f401])).

fof(f2336,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2327,f131])).

fof(f2327,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f689,f126])).

fof(f689,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(k1_tops_1(X7,X6),X6)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f148,f269])).

fof(f148,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f147,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1921,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f1920,f218,f118,f222])).

fof(f1920,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1919,f219])).

fof(f1919,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f120,f76])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f668,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f667])).

fof(f667,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f666,f131])).

fof(f666,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f659,f126])).

fof(f659,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f289,f220])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f218])).

fof(f256,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f251,f134,f129,f124,f253])).

fof(f253,plain,
    ( spl3_13
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f134,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f251,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f250,f136])).

fof(f136,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f250,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f247,f131])).

fof(f247,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f126])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f145,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f138,f124,f142])).

fof(f138,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f91,f126])).

fof(f137,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f71,f134])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f132,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f72,f129])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f127,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f73,f124])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f122,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f74,f118,f114])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f121,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f118,f114])).

fof(f75,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15581)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (15583)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15579)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (15589)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (15580)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (15596)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (15590)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (15577)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (15578)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (15605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (15591)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (15604)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (15601)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (15597)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (15602)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (15582)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (15598)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (15588)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (15593)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (15603)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (15606)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (15594)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (15595)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (15592)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (15599)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (15585)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (15587)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (15600)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (15584)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.72/0.60  % (15586)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 3.12/0.82  % (15601)Time limit reached!
% 3.12/0.82  % (15601)------------------------------
% 3.12/0.82  % (15601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.82  % (15601)Termination reason: Time limit
% 3.12/0.82  
% 3.12/0.82  % (15601)Memory used [KB]: 13688
% 3.12/0.82  % (15601)Time elapsed: 0.411 s
% 3.12/0.82  % (15601)------------------------------
% 3.12/0.82  % (15601)------------------------------
% 3.12/0.84  % (15579)Time limit reached!
% 3.12/0.84  % (15579)------------------------------
% 3.12/0.84  % (15579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.84  % (15579)Termination reason: Time limit
% 3.12/0.84  
% 3.12/0.84  % (15579)Memory used [KB]: 6780
% 3.12/0.84  % (15579)Time elapsed: 0.428 s
% 3.12/0.84  % (15579)------------------------------
% 3.12/0.84  % (15579)------------------------------
% 3.86/0.91  % (15606)Time limit reached!
% 3.86/0.91  % (15606)------------------------------
% 3.86/0.91  % (15606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.91  % (15606)Termination reason: Time limit
% 3.86/0.91  % (15606)Termination phase: Saturation
% 3.86/0.91  
% 3.86/0.91  % (15606)Memory used [KB]: 3965
% 3.86/0.91  % (15606)Time elapsed: 0.500 s
% 3.86/0.91  % (15606)------------------------------
% 3.86/0.91  % (15606)------------------------------
% 4.26/0.93  % (15591)Time limit reached!
% 4.26/0.93  % (15591)------------------------------
% 4.26/0.93  % (15591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (15583)Time limit reached!
% 4.26/0.93  % (15583)------------------------------
% 4.26/0.93  % (15583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.94  % (15583)Termination reason: Time limit
% 4.26/0.94  
% 4.26/0.94  % (15583)Memory used [KB]: 15351
% 4.26/0.94  % (15583)Time elapsed: 0.519 s
% 4.26/0.94  % (15583)------------------------------
% 4.26/0.94  % (15583)------------------------------
% 4.26/0.94  % (15591)Termination reason: Time limit
% 4.26/0.94  % (15591)Termination phase: Saturation
% 4.26/0.94  
% 4.26/0.94  % (15591)Memory used [KB]: 6140
% 4.26/0.94  % (15591)Time elapsed: 0.500 s
% 4.26/0.94  % (15591)------------------------------
% 4.26/0.94  % (15591)------------------------------
% 4.49/0.96  % (15628)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.49/1.01  % (15629)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.49/1.02  % (15598)Refutation found. Thanks to Tanya!
% 4.49/1.02  % SZS status Theorem for theBenchmark
% 4.49/1.02  % SZS output start Proof for theBenchmark
% 4.49/1.02  fof(f3773,plain,(
% 4.49/1.02    $false),
% 4.49/1.02    inference(avatar_sat_refutation,[],[f121,f122,f127,f132,f137,f145,f256,f668,f1921,f2337,f2389,f2416,f2523,f2528,f2534,f2555,f2571,f2577,f2582,f2764,f3741,f3769])).
% 4.49/1.02  fof(f3769,plain,(
% 4.49/1.02    ~spl3_3 | ~spl3_4 | spl3_77 | ~spl3_131),
% 4.49/1.02    inference(avatar_contradiction_clause,[],[f3768])).
% 4.49/1.02  fof(f3768,plain,(
% 4.49/1.02    $false | (~spl3_3 | ~spl3_4 | spl3_77 | ~spl3_131)),
% 4.49/1.02    inference(subsumption_resolution,[],[f3767,f131])).
% 4.49/1.02  fof(f131,plain,(
% 4.49/1.02    l1_pre_topc(sK0) | ~spl3_4),
% 4.49/1.02    inference(avatar_component_clause,[],[f129])).
% 4.49/1.02  fof(f129,plain,(
% 4.49/1.02    spl3_4 <=> l1_pre_topc(sK0)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.49/1.02  fof(f3767,plain,(
% 4.49/1.02    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_77 | ~spl3_131)),
% 4.49/1.02    inference(subsumption_resolution,[],[f3766,f126])).
% 4.49/1.02  fof(f126,plain,(
% 4.49/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 4.49/1.02    inference(avatar_component_clause,[],[f124])).
% 4.49/1.02  fof(f124,plain,(
% 4.49/1.02    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.49/1.02  fof(f3766,plain,(
% 4.49/1.02    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_77 | ~spl3_131)),
% 4.49/1.02    inference(subsumption_resolution,[],[f3749,f2351])).
% 4.49/1.02  fof(f2351,plain,(
% 4.49/1.02    sK1 != k1_tops_1(sK0,sK1) | spl3_77),
% 4.49/1.02    inference(avatar_component_clause,[],[f2350])).
% 4.49/1.02  fof(f2350,plain,(
% 4.49/1.02    spl3_77 <=> sK1 = k1_tops_1(sK0,sK1)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 4.49/1.02  fof(f3749,plain,(
% 4.49/1.02    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_131),
% 4.49/1.02    inference(superposition,[],[f269,f3740])).
% 4.49/1.02  fof(f3740,plain,(
% 4.49/1.02    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_131),
% 4.49/1.02    inference(avatar_component_clause,[],[f3738])).
% 4.49/1.02  fof(f3738,plain,(
% 4.49/1.02    spl3_131 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).
% 4.49/1.02  fof(f269,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(duplicate_literal_removal,[],[f268])).
% 4.49/1.02  fof(f268,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(superposition,[],[f76,f83])).
% 4.49/1.02  fof(f83,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f40])).
% 4.49/1.02  fof(f40,plain,(
% 4.49/1.02    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.49/1.02    inference(ennf_transformation,[],[f32])).
% 4.49/1.02  fof(f32,axiom,(
% 4.49/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 4.49/1.02  fof(f76,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f37])).
% 4.49/1.02  fof(f37,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f22])).
% 4.49/1.02  fof(f22,axiom,(
% 4.49/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 4.49/1.02  fof(f3741,plain,(
% 4.49/1.02    spl3_86 | spl3_131 | ~spl3_66 | ~spl3_72),
% 4.49/1.02    inference(avatar_split_clause,[],[f3736,f1907,f1876,f3738,f2625])).
% 4.49/1.02  fof(f2625,plain,(
% 4.49/1.02    spl3_86 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 4.49/1.02  fof(f1876,plain,(
% 4.49/1.02    spl3_66 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 4.49/1.02  fof(f1907,plain,(
% 4.49/1.02    spl3_72 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 4.49/1.02  fof(f3736,plain,(
% 4.49/1.02    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_66 | ~spl3_72)),
% 4.49/1.02    inference(subsumption_resolution,[],[f3716,f1878])).
% 4.49/1.02  fof(f1878,plain,(
% 4.49/1.02    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_66),
% 4.49/1.02    inference(avatar_component_clause,[],[f1876])).
% 4.49/1.02  fof(f3716,plain,(
% 4.49/1.02    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_72),
% 4.49/1.02    inference(superposition,[],[f787,f1909])).
% 4.49/1.02  fof(f1909,plain,(
% 4.49/1.02    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_72),
% 4.49/1.02    inference(avatar_component_clause,[],[f1907])).
% 4.49/1.02  fof(f787,plain,(
% 4.49/1.02    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 4.49/1.02    inference(subsumption_resolution,[],[f782,f93])).
% 4.49/1.02  fof(f93,plain,(
% 4.49/1.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f51])).
% 4.49/1.02  fof(f51,plain,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f14])).
% 4.49/1.02  fof(f14,axiom,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.49/1.02  fof(f782,plain,(
% 4.49/1.02    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 4.49/1.02    inference(superposition,[],[f296,f76])).
% 4.49/1.02  fof(f296,plain,(
% 4.49/1.02    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 4.49/1.02    inference(subsumption_resolution,[],[f292,f93])).
% 4.49/1.02  fof(f292,plain,(
% 4.49/1.02    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 4.49/1.02    inference(superposition,[],[f85,f105])).
% 4.49/1.02  fof(f105,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f56])).
% 4.49/1.02  fof(f56,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f18])).
% 4.49/1.02  fof(f18,axiom,(
% 4.49/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 4.49/1.02  fof(f85,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f42])).
% 4.49/1.02  fof(f42,plain,(
% 4.49/1.02    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f23])).
% 4.49/1.02  fof(f23,axiom,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 4.49/1.02  fof(f2764,plain,(
% 4.49/1.02    ~spl3_86),
% 4.49/1.02    inference(avatar_contradiction_clause,[],[f2729])).
% 4.49/1.02  fof(f2729,plain,(
% 4.49/1.02    $false | ~spl3_86),
% 4.49/1.02    inference(unit_resulting_resolution,[],[f149,f94,f2626,f107])).
% 4.49/1.02  fof(f107,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f60])).
% 4.49/1.02  fof(f60,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(flattening,[],[f59])).
% 4.49/1.02  fof(f59,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.49/1.02    inference(ennf_transformation,[],[f15])).
% 4.49/1.02  fof(f15,axiom,(
% 4.49/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 4.49/1.02  fof(f2626,plain,(
% 4.49/1.02    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_86),
% 4.49/1.02    inference(avatar_component_clause,[],[f2625])).
% 4.49/1.02  fof(f94,plain,(
% 4.49/1.02    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f70])).
% 4.49/1.02  fof(f70,plain,(
% 4.49/1.02    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 4.49/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f69])).
% 4.49/1.02  fof(f69,plain,(
% 4.49/1.02    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 4.49/1.02    introduced(choice_axiom,[])).
% 4.49/1.02  fof(f17,axiom,(
% 4.49/1.02    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 4.49/1.02  fof(f149,plain,(
% 4.49/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(superposition,[],[f147,f98])).
% 4.49/1.02  fof(f98,plain,(
% 4.49/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.49/1.02    inference(cnf_transformation,[],[f7])).
% 4.49/1.02  fof(f7,axiom,(
% 4.49/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 4.49/1.02  fof(f147,plain,(
% 4.49/1.02    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(backward_demodulation,[],[f109,f97])).
% 4.49/1.02  fof(f97,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f21])).
% 4.49/1.02  fof(f21,axiom,(
% 4.49/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 4.49/1.02  fof(f109,plain,(
% 4.49/1.02    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f16])).
% 4.49/1.02  fof(f16,axiom,(
% 4.49/1.02    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 4.49/1.02  fof(f2582,plain,(
% 4.49/1.02    ~spl3_76 | spl3_77 | ~spl3_18),
% 4.49/1.02    inference(avatar_split_clause,[],[f2581,f401,f2350,f2346])).
% 4.49/1.02  fof(f2346,plain,(
% 4.49/1.02    spl3_76 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 4.49/1.02  fof(f401,plain,(
% 4.49/1.02    spl3_18 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 4.49/1.02  fof(f2581,plain,(
% 4.49/1.02    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_18),
% 4.49/1.02    inference(resolution,[],[f402,f79])).
% 4.49/1.02  fof(f79,plain,(
% 4.49/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f67])).
% 4.49/1.02  fof(f67,plain,(
% 4.49/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.49/1.02    inference(flattening,[],[f66])).
% 4.49/1.02  fof(f66,plain,(
% 4.49/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.49/1.02    inference(nnf_transformation,[],[f1])).
% 4.49/1.02  fof(f1,axiom,(
% 4.49/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.49/1.02  fof(f402,plain,(
% 4.49/1.02    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_18),
% 4.49/1.02    inference(avatar_component_clause,[],[f401])).
% 4.49/1.02  fof(f2577,plain,(
% 4.49/1.02    spl3_71 | ~spl3_79),
% 4.49/1.02    inference(avatar_contradiction_clause,[],[f2576])).
% 4.49/1.02  fof(f2576,plain,(
% 4.49/1.02    $false | (spl3_71 | ~spl3_79)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2574,f2415])).
% 4.49/1.02  fof(f2415,plain,(
% 4.49/1.02    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_79),
% 4.49/1.02    inference(avatar_component_clause,[],[f2413])).
% 4.49/1.02  fof(f2413,plain,(
% 4.49/1.02    spl3_79 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 4.49/1.02  fof(f2574,plain,(
% 4.49/1.02    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_71),
% 4.49/1.02    inference(resolution,[],[f1905,f92])).
% 4.49/1.02  fof(f92,plain,(
% 4.49/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f68])).
% 4.49/1.02  fof(f68,plain,(
% 4.49/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.49/1.02    inference(nnf_transformation,[],[f25])).
% 4.49/1.02  fof(f25,axiom,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 4.49/1.02  fof(f1905,plain,(
% 4.49/1.02    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_71),
% 4.49/1.02    inference(avatar_component_clause,[],[f1903])).
% 4.49/1.02  fof(f1903,plain,(
% 4.49/1.02    spl3_71 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 4.49/1.02  fof(f2571,plain,(
% 4.49/1.02    ~spl3_71 | spl3_72 | ~spl3_10),
% 4.49/1.02    inference(avatar_split_clause,[],[f2549,f222,f1907,f1903])).
% 4.49/1.02  fof(f222,plain,(
% 4.49/1.02    spl3_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 4.49/1.02  fof(f2549,plain,(
% 4.49/1.02    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 4.49/1.02    inference(superposition,[],[f212,f224])).
% 4.49/1.02  fof(f224,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_10),
% 4.49/1.02    inference(avatar_component_clause,[],[f222])).
% 4.49/1.02  fof(f212,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(duplicate_literal_removal,[],[f208])).
% 4.49/1.02  fof(f208,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(superposition,[],[f80,f81])).
% 4.49/1.02  fof(f81,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f39])).
% 4.49/1.02  fof(f39,plain,(
% 4.49/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f13])).
% 4.49/1.02  fof(f13,axiom,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 4.49/1.02  fof(f80,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f38])).
% 4.49/1.02  fof(f38,plain,(
% 4.49/1.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f19])).
% 4.49/1.02  fof(f19,axiom,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 4.49/1.02  fof(f2555,plain,(
% 4.49/1.02    spl3_66 | ~spl3_10),
% 4.49/1.02    inference(avatar_split_clause,[],[f2543,f222,f1876])).
% 4.49/1.02  fof(f2543,plain,(
% 4.49/1.02    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 4.49/1.02    inference(superposition,[],[f147,f224])).
% 4.49/1.02  fof(f2534,plain,(
% 4.49/1.02    spl3_10 | ~spl3_2 | ~spl3_9),
% 4.49/1.02    inference(avatar_split_clause,[],[f2533,f218,f118,f222])).
% 4.49/1.02  fof(f118,plain,(
% 4.49/1.02    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.49/1.02  fof(f218,plain,(
% 4.49/1.02    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 4.49/1.02  fof(f2533,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2530,f219])).
% 4.49/1.02  fof(f219,plain,(
% 4.49/1.02    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 4.49/1.02    inference(avatar_component_clause,[],[f218])).
% 4.49/1.02  fof(f2530,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.49/1.02    inference(superposition,[],[f76,f119])).
% 4.49/1.02  fof(f119,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 4.49/1.02    inference(avatar_component_clause,[],[f118])).
% 4.49/1.02  fof(f2528,plain,(
% 4.49/1.02    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 4.49/1.02    introduced(theory_tautology_sat_conflict,[])).
% 4.49/1.02  fof(f2523,plain,(
% 4.49/1.02    ~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_77),
% 4.49/1.02    inference(avatar_contradiction_clause,[],[f2522])).
% 4.49/1.02  fof(f2522,plain,(
% 4.49/1.02    $false | (~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_77)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2521,f131])).
% 4.49/1.02  fof(f2521,plain,(
% 4.49/1.02    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10 | ~spl3_77)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2520,f126])).
% 4.49/1.02  fof(f2520,plain,(
% 4.49/1.02    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_10 | ~spl3_77)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2517,f223])).
% 4.49/1.02  fof(f223,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_10),
% 4.49/1.02    inference(avatar_component_clause,[],[f222])).
% 4.49/1.02  fof(f2517,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_77),
% 4.49/1.02    inference(superposition,[],[f924,f2352])).
% 4.49/1.02  fof(f2352,plain,(
% 4.49/1.02    sK1 = k1_tops_1(sK0,sK1) | ~spl3_77),
% 4.49/1.02    inference(avatar_component_clause,[],[f2350])).
% 4.49/1.02  fof(f924,plain,(
% 4.49/1.02    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.49/1.02    inference(subsumption_resolution,[],[f298,f289])).
% 4.49/1.02  fof(f289,plain,(
% 4.49/1.02    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.49/1.02    inference(subsumption_resolution,[],[f282,f88])).
% 4.49/1.02  fof(f88,plain,(
% 4.49/1.02    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f46])).
% 4.49/1.02  fof(f46,plain,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.49/1.02    inference(flattening,[],[f45])).
% 4.49/1.02  fof(f45,plain,(
% 4.49/1.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f26])).
% 4.49/1.02  fof(f26,axiom,(
% 4.49/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 4.49/1.02  fof(f282,plain,(
% 4.49/1.02    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.49/1.02    inference(duplicate_literal_removal,[],[f281])).
% 4.49/1.02  fof(f281,plain,(
% 4.49/1.02    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.49/1.02    inference(superposition,[],[f107,f87])).
% 4.49/1.02  fof(f87,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f44])).
% 4.49/1.02  fof(f44,plain,(
% 4.49/1.02    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.49/1.02    inference(ennf_transformation,[],[f31])).
% 4.49/1.02  fof(f31,axiom,(
% 4.49/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 4.49/1.02  fof(f298,plain,(
% 4.49/1.02    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.49/1.02    inference(superposition,[],[f86,f76])).
% 4.49/1.02  fof(f86,plain,(
% 4.49/1.02    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f43])).
% 4.49/1.02  fof(f43,plain,(
% 4.49/1.02    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.49/1.02    inference(ennf_transformation,[],[f28])).
% 4.49/1.02  fof(f28,axiom,(
% 4.49/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 4.49/1.02  fof(f2416,plain,(
% 4.49/1.02    spl3_79 | ~spl3_3 | ~spl3_4),
% 4.49/1.02    inference(avatar_split_clause,[],[f2411,f129,f124,f2413])).
% 4.49/1.02  fof(f2411,plain,(
% 4.49/1.02    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2401,f131])).
% 4.49/1.02  fof(f2401,plain,(
% 4.49/1.02    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.49/1.02    inference(resolution,[],[f715,f126])).
% 4.49/1.02  fof(f715,plain,(
% 4.49/1.02    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(X3,k2_pre_topc(X4,X3)) | ~l1_pre_topc(X4)) )),
% 4.49/1.02    inference(superposition,[],[f101,f287])).
% 4.49/1.02  fof(f287,plain,(
% 4.49/1.02    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.49/1.02    inference(subsumption_resolution,[],[f284,f88])).
% 4.49/1.02  fof(f284,plain,(
% 4.49/1.02    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.49/1.02    inference(duplicate_literal_removal,[],[f279])).
% 4.49/1.02  fof(f279,plain,(
% 4.49/1.02    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.49/1.02    inference(superposition,[],[f87,f106])).
% 4.49/1.02  fof(f106,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f58])).
% 4.49/1.02  fof(f58,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.49/1.02    inference(flattening,[],[f57])).
% 4.49/1.02  fof(f57,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.49/1.02    inference(ennf_transformation,[],[f20])).
% 4.49/1.02  fof(f20,axiom,(
% 4.49/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.49/1.02  fof(f101,plain,(
% 4.49/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.49/1.02    inference(cnf_transformation,[],[f10])).
% 4.49/1.02  fof(f10,axiom,(
% 4.49/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.49/1.02  fof(f2389,plain,(
% 4.49/1.02    ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76),
% 4.49/1.02    inference(avatar_contradiction_clause,[],[f2388])).
% 4.49/1.02  fof(f2388,plain,(
% 4.49/1.02    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2387,f111])).
% 4.49/1.02  fof(f111,plain,(
% 4.49/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.49/1.02    inference(equality_resolution,[],[f78])).
% 4.49/1.02  fof(f78,plain,(
% 4.49/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.49/1.02    inference(cnf_transformation,[],[f67])).
% 4.49/1.02  fof(f2387,plain,(
% 4.49/1.02    ~r1_tarski(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2379,f115])).
% 4.49/1.02  fof(f115,plain,(
% 4.49/1.02    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 4.49/1.02    inference(avatar_component_clause,[],[f114])).
% 4.49/1.02  fof(f114,plain,(
% 4.49/1.02    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.49/1.02  fof(f2379,plain,(
% 4.49/1.02    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76)),
% 4.49/1.02    inference(resolution,[],[f2348,f329])).
% 4.49/1.02  fof(f329,plain,(
% 4.49/1.02    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 4.49/1.02    inference(subsumption_resolution,[],[f321,f186])).
% 4.49/1.02  fof(f186,plain,(
% 4.49/1.02    ( ! [X15] : (r1_tarski(X15,u1_struct_0(sK0)) | ~r1_tarski(X15,sK1)) ) | ~spl3_6),
% 4.49/1.02    inference(resolution,[],[f99,f144])).
% 4.49/1.02  fof(f144,plain,(
% 4.49/1.02    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 4.49/1.02    inference(avatar_component_clause,[],[f142])).
% 4.49/1.02  fof(f142,plain,(
% 4.49/1.02    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 4.49/1.02  fof(f99,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f55])).
% 4.49/1.02  fof(f55,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.49/1.02    inference(flattening,[],[f54])).
% 4.49/1.02  fof(f54,plain,(
% 4.49/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.49/1.02    inference(ennf_transformation,[],[f4])).
% 4.49/1.02  fof(f4,axiom,(
% 4.49/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.49/1.02  fof(f321,plain,(
% 4.49/1.02    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_4)),
% 4.49/1.02    inference(resolution,[],[f315,f92])).
% 4.49/1.02  fof(f315,plain,(
% 4.49/1.02    ( ! [X18] : (~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~r1_tarski(X18,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 4.49/1.02    inference(subsumption_resolution,[],[f311,f131])).
% 4.49/1.02  fof(f311,plain,(
% 4.49/1.02    ( ! [X18] : (~r1_tarski(X18,sK1) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 4.49/1.02    inference(resolution,[],[f90,f126])).
% 4.49/1.02  fof(f90,plain,(
% 4.49/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f50])).
% 4.49/1.02  fof(f50,plain,(
% 4.49/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.49/1.02    inference(flattening,[],[f49])).
% 4.49/1.02  fof(f49,plain,(
% 4.49/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.49/1.02    inference(ennf_transformation,[],[f29])).
% 4.49/1.02  fof(f29,axiom,(
% 4.49/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 4.49/1.02  fof(f2348,plain,(
% 4.49/1.02    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_76),
% 4.49/1.02    inference(avatar_component_clause,[],[f2346])).
% 4.49/1.02  fof(f2337,plain,(
% 4.49/1.02    spl3_18 | ~spl3_3 | ~spl3_4),
% 4.49/1.02    inference(avatar_split_clause,[],[f2336,f129,f124,f401])).
% 4.49/1.02  fof(f2336,plain,(
% 4.49/1.02    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 4.49/1.02    inference(subsumption_resolution,[],[f2327,f131])).
% 4.49/1.02  fof(f2327,plain,(
% 4.49/1.02    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.49/1.02    inference(resolution,[],[f689,f126])).
% 4.49/1.02  fof(f689,plain,(
% 4.49/1.02    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(k1_tops_1(X7,X6),X6) | ~l1_pre_topc(X7)) )),
% 4.49/1.02    inference(superposition,[],[f148,f269])).
% 4.49/1.02  fof(f148,plain,(
% 4.49/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.49/1.02    inference(resolution,[],[f147,f91])).
% 4.49/1.02  fof(f91,plain,(
% 4.49/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f68])).
% 4.49/1.02  fof(f1921,plain,(
% 4.49/1.02    ~spl3_10 | spl3_2 | ~spl3_9),
% 4.49/1.02    inference(avatar_split_clause,[],[f1920,f218,f118,f222])).
% 4.49/1.02  fof(f1920,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_9)),
% 4.49/1.02    inference(subsumption_resolution,[],[f1919,f219])).
% 4.49/1.02  fof(f1919,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 4.49/1.02    inference(superposition,[],[f120,f76])).
% 4.49/1.02  fof(f120,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 4.49/1.02    inference(avatar_component_clause,[],[f118])).
% 4.49/1.02  fof(f668,plain,(
% 4.49/1.02    ~spl3_3 | ~spl3_4 | spl3_9),
% 4.49/1.02    inference(avatar_contradiction_clause,[],[f667])).
% 4.49/1.02  fof(f667,plain,(
% 4.49/1.02    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 4.49/1.02    inference(subsumption_resolution,[],[f666,f131])).
% 4.49/1.02  fof(f666,plain,(
% 4.49/1.02    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 4.49/1.02    inference(subsumption_resolution,[],[f659,f126])).
% 4.49/1.02  fof(f659,plain,(
% 4.49/1.02    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 4.49/1.02    inference(resolution,[],[f289,f220])).
% 4.49/1.02  fof(f220,plain,(
% 4.49/1.02    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 4.49/1.02    inference(avatar_component_clause,[],[f218])).
% 4.49/1.02  fof(f256,plain,(
% 4.49/1.02    spl3_13 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 4.49/1.02    inference(avatar_split_clause,[],[f251,f134,f129,f124,f253])).
% 4.49/1.02  fof(f253,plain,(
% 4.49/1.02    spl3_13 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 4.49/1.02  fof(f134,plain,(
% 4.49/1.02    spl3_5 <=> v2_pre_topc(sK0)),
% 4.49/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.49/1.02  fof(f251,plain,(
% 4.49/1.02    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 4.49/1.02    inference(subsumption_resolution,[],[f250,f136])).
% 4.49/1.02  fof(f136,plain,(
% 4.49/1.02    v2_pre_topc(sK0) | ~spl3_5),
% 4.49/1.02    inference(avatar_component_clause,[],[f134])).
% 4.49/1.02  fof(f250,plain,(
% 4.49/1.02    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 4.49/1.02    inference(subsumption_resolution,[],[f247,f131])).
% 4.49/1.02  fof(f247,plain,(
% 4.49/1.02    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 4.49/1.02    inference(resolution,[],[f89,f126])).
% 4.49/1.02  fof(f89,plain,(
% 4.49/1.02    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.49/1.02    inference(cnf_transformation,[],[f48])).
% 4.49/1.02  fof(f48,plain,(
% 4.49/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.49/1.02    inference(flattening,[],[f47])).
% 4.49/1.02  fof(f47,plain,(
% 4.49/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f27])).
% 4.49/1.02  fof(f27,axiom,(
% 4.49/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 4.49/1.02  fof(f145,plain,(
% 4.49/1.02    spl3_6 | ~spl3_3),
% 4.49/1.02    inference(avatar_split_clause,[],[f138,f124,f142])).
% 4.49/1.02  fof(f138,plain,(
% 4.49/1.02    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 4.49/1.02    inference(resolution,[],[f91,f126])).
% 4.49/1.02  fof(f137,plain,(
% 4.49/1.02    spl3_5),
% 4.49/1.02    inference(avatar_split_clause,[],[f71,f134])).
% 4.49/1.02  fof(f71,plain,(
% 4.49/1.02    v2_pre_topc(sK0)),
% 4.49/1.02    inference(cnf_transformation,[],[f65])).
% 4.49/1.02  fof(f65,plain,(
% 4.49/1.02    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.49/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).
% 4.49/1.02  fof(f63,plain,(
% 4.49/1.02    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.49/1.02    introduced(choice_axiom,[])).
% 4.49/1.02  fof(f64,plain,(
% 4.49/1.02    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.49/1.02    introduced(choice_axiom,[])).
% 4.49/1.02  fof(f62,plain,(
% 4.49/1.02    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.49/1.02    inference(flattening,[],[f61])).
% 4.49/1.02  fof(f61,plain,(
% 4.49/1.02    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.49/1.02    inference(nnf_transformation,[],[f36])).
% 4.49/1.02  fof(f36,plain,(
% 4.49/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.49/1.02    inference(flattening,[],[f35])).
% 4.49/1.02  fof(f35,plain,(
% 4.49/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.49/1.02    inference(ennf_transformation,[],[f34])).
% 4.49/1.02  fof(f34,negated_conjecture,(
% 4.49/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.49/1.02    inference(negated_conjecture,[],[f33])).
% 4.49/1.02  fof(f33,conjecture,(
% 4.49/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.49/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 4.49/1.02  fof(f132,plain,(
% 4.49/1.02    spl3_4),
% 4.49/1.02    inference(avatar_split_clause,[],[f72,f129])).
% 4.49/1.02  fof(f72,plain,(
% 4.49/1.02    l1_pre_topc(sK0)),
% 4.49/1.02    inference(cnf_transformation,[],[f65])).
% 4.49/1.02  fof(f127,plain,(
% 4.49/1.02    spl3_3),
% 4.49/1.02    inference(avatar_split_clause,[],[f73,f124])).
% 4.49/1.02  fof(f73,plain,(
% 4.49/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.49/1.02    inference(cnf_transformation,[],[f65])).
% 4.49/1.02  fof(f122,plain,(
% 4.49/1.02    spl3_1 | spl3_2),
% 4.49/1.02    inference(avatar_split_clause,[],[f74,f118,f114])).
% 4.49/1.02  fof(f74,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 4.49/1.02    inference(cnf_transformation,[],[f65])).
% 4.49/1.02  fof(f121,plain,(
% 4.49/1.02    ~spl3_1 | ~spl3_2),
% 4.49/1.02    inference(avatar_split_clause,[],[f75,f118,f114])).
% 4.49/1.02  fof(f75,plain,(
% 4.49/1.02    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 4.49/1.02    inference(cnf_transformation,[],[f65])).
% 4.49/1.02  % SZS output end Proof for theBenchmark
% 4.49/1.02  % (15598)------------------------------
% 4.49/1.02  % (15598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.49/1.02  % (15598)Termination reason: Refutation
% 4.49/1.02  
% 4.49/1.02  % (15598)Memory used [KB]: 12792
% 4.49/1.02  % (15598)Time elapsed: 0.599 s
% 4.49/1.02  % (15598)------------------------------
% 4.49/1.02  % (15598)------------------------------
% 4.85/1.03  % (15576)Success in time 0.658 s
%------------------------------------------------------------------------------
