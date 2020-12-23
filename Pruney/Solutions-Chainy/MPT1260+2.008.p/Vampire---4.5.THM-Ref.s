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
% DateTime   : Thu Dec  3 13:11:33 EST 2020

% Result     : Theorem 4.68s
% Output     : Refutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 382 expanded)
%              Number of leaves         :   45 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  614 (1193 expanded)
%              Number of equality atoms :   96 ( 221 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3596,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f122,f127,f132,f137,f145,f265,f580,f671,f2028,f2311,f2334,f2475,f2488,f2500,f2518,f2538,f2543,f2636,f3476,f3558,f3595])).

fof(f3595,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3558,plain,
    ( spl3_97
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_138 ),
    inference(avatar_split_clause,[],[f3557,f3473,f129,f124,f2370])).

fof(f2370,plain,
    ( spl3_97
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f124,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f129,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f3473,plain,
    ( spl3_138
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).

fof(f3557,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_138 ),
    inference(subsumption_resolution,[],[f3556,f131])).

fof(f131,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f3556,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_138 ),
    inference(subsumption_resolution,[],[f3535,f126])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f3535,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_138 ),
    inference(superposition,[],[f286,f3475])).

fof(f3475,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_138 ),
    inference(avatar_component_clause,[],[f3473])).

fof(f286,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f76,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3476,plain,
    ( spl3_76
    | spl3_138
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f3471,f668,f631,f3473,f1905])).

fof(f1905,plain,
    ( spl3_76
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f631,plain,
    ( spl3_23
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f668,plain,
    ( spl3_31
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f3471,plain,
    ( ! [X16] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f3445,f633])).

fof(f633,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f631])).

fof(f3445,plain,
    ( ! [X16] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_31 ),
    inference(superposition,[],[f780,f670])).

fof(f670,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f668])).

fof(f780,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f775,f94])).

fof(f94,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f775,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f314,f76])).

fof(f314,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f310,f94])).

fof(f310,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f2636,plain,(
    ~ spl3_76 ),
    inference(avatar_contradiction_clause,[],[f2601])).

fof(f2601,plain,
    ( $false
    | ~ spl3_76 ),
    inference(unit_resulting_resolution,[],[f149,f95,f1906,f107])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1906,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f95,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f149,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f147,f99])).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f147,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f109,f98])).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f109,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f2543,plain,
    ( spl3_30
    | ~ spl3_75 ),
    inference(avatar_contradiction_clause,[],[f2542])).

fof(f2542,plain,
    ( $false
    | spl3_30
    | ~ spl3_75 ),
    inference(subsumption_resolution,[],[f2540,f1897])).

fof(f1897,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f1895,plain,
    ( spl3_75
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f2540,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_30 ),
    inference(resolution,[],[f666,f93])).

fof(f93,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f666,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f664])).

fof(f664,plain,
    ( spl3_30
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f2538,plain,
    ( ~ spl3_96
    | spl3_97
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f2537,f1813,f2370,f2366])).

fof(f2366,plain,
    ( spl3_96
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1813,plain,
    ( spl3_65
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f2537,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_65 ),
    inference(resolution,[],[f1814,f79])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1814,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f1813])).

fof(f2518,plain,
    ( spl3_23
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2504,f239,f631])).

fof(f239,plain,
    ( spl3_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f2504,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f147,f241])).

fof(f241,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f239])).

fof(f2500,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f2499,f235,f118,f239])).

fof(f118,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f235,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f2499,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f2496,f236])).

fof(f236,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f235])).

fof(f2496,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f76,f119])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f2488,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_97 ),
    inference(avatar_contradiction_clause,[],[f2487])).

fof(f2487,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_97 ),
    inference(subsumption_resolution,[],[f2486,f131])).

fof(f2486,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10
    | ~ spl3_97 ),
    inference(subsumption_resolution,[],[f2485,f126])).

fof(f2485,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10
    | ~ spl3_97 ),
    inference(subsumption_resolution,[],[f2482,f240])).

fof(f240,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f239])).

fof(f2482,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_97 ),
    inference(superposition,[],[f927,f2372])).

fof(f2372,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_97 ),
    inference(avatar_component_clause,[],[f2370])).

fof(f927,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f318,f307])).

fof(f307,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f300,f89])).

fof(f89,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f300,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f107,f88])).

fof(f88,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f318,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2475,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_96 ),
    inference(avatar_contradiction_clause,[],[f2474])).

fof(f2474,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_96 ),
    inference(subsumption_resolution,[],[f2473,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2473,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_96 ),
    inference(subsumption_resolution,[],[f2465,f115])).

fof(f115,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2465,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_96 ),
    inference(resolution,[],[f2368,f342])).

fof(f342,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f334,f191])).

fof(f191,plain,
    ( ! [X11] :
        ( r1_tarski(X11,u1_struct_0(sK0))
        | ~ r1_tarski(X11,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f100,f144])).

fof(f144,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f100,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f334,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f333,f93])).

fof(f333,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X18,sK0)
        | r1_tarski(X18,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X18,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f329,f131])).

fof(f329,plain,
    ( ! [X18] :
        ( ~ r1_tarski(X18,sK1)
        | ~ v3_pre_topc(X18,sK0)
        | r1_tarski(X18,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f91,f126])).

fof(f91,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f2368,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_96 ),
    inference(avatar_component_clause,[],[f2366])).

fof(f2334,plain,
    ( spl3_75
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2333,f129,f124,f1895])).

fof(f2333,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2323,f131])).

fof(f2323,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f704,f126])).

fof(f704,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(X3,k2_pre_topc(X4,X3))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f101,f305])).

fof(f305,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f302,f89])).

fof(f302,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f88,f106])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2311,plain,
    ( spl3_65
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2310,f129,f124,f1813])).

fof(f2310,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2300,f131])).

fof(f2300,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f681,f126])).

fof(f681,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(k1_tops_1(X7,X6),X6)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f148,f286])).

fof(f148,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f147,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2028,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_2 ),
    inference(avatar_split_clause,[],[f2027,f118,f239,f235])).

fof(f2027,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f120,f76])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f671,plain,
    ( ~ spl3_30
    | spl3_31
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f615,f239,f668,f664])).

fof(f615,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f222,f241])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f580,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f578,f131])).

fof(f578,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f571,f126])).

fof(f571,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f307,f237])).

fof(f237,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f235])).

fof(f265,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f260,f134,f129,f124,f262])).

fof(f262,plain,
    ( spl3_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f134,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f260,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f259,f136])).

fof(f136,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f259,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f256,f131])).

fof(f256,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f90,f126])).

fof(f90,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f145,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f138,f124,f142])).

fof(f138,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f92,f126])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:47:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.51  % (7030)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (7029)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (7038)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (7024)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (7022)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (7033)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (7027)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (7045)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (7037)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (7050)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (7023)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (7041)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (7034)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (7051)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (7028)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (7032)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (7046)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (7025)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (7040)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (7035)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (7042)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (7031)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (7048)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (7049)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (7036)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (7039)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (7026)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.55  % (7043)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (7044)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.57  % (7047)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 3.29/0.81  % (7046)Time limit reached!
% 3.29/0.81  % (7046)------------------------------
% 3.29/0.81  % (7046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.81  % (7046)Termination reason: Time limit
% 3.29/0.81  % (7046)Termination phase: Saturation
% 3.29/0.81  
% 3.29/0.81  % (7046)Memory used [KB]: 13432
% 3.29/0.81  % (7046)Time elapsed: 0.400 s
% 3.29/0.81  % (7046)------------------------------
% 3.29/0.81  % (7046)------------------------------
% 3.72/0.84  % (7024)Time limit reached!
% 3.72/0.84  % (7024)------------------------------
% 3.72/0.84  % (7024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.84  % (7024)Termination reason: Time limit
% 3.72/0.84  
% 3.72/0.84  % (7024)Memory used [KB]: 6780
% 3.72/0.84  % (7024)Time elapsed: 0.433 s
% 3.72/0.84  % (7024)------------------------------
% 3.72/0.84  % (7024)------------------------------
% 3.85/0.91  % (7051)Time limit reached!
% 3.85/0.91  % (7051)------------------------------
% 3.85/0.91  % (7051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.92  % (7051)Termination reason: Time limit
% 4.33/0.92  
% 4.33/0.92  % (7051)Memory used [KB]: 3965
% 4.33/0.92  % (7051)Time elapsed: 0.509 s
% 4.33/0.92  % (7051)------------------------------
% 4.33/0.92  % (7051)------------------------------
% 4.33/0.93  % (7028)Time limit reached!
% 4.33/0.93  % (7028)------------------------------
% 4.33/0.93  % (7028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.93  % (7028)Termination reason: Time limit
% 4.33/0.93  % (7028)Termination phase: Saturation
% 4.33/0.93  
% 4.33/0.93  % (7028)Memory used [KB]: 15607
% 4.33/0.93  % (7028)Time elapsed: 0.500 s
% 4.33/0.93  % (7028)------------------------------
% 4.33/0.93  % (7028)------------------------------
% 4.33/0.93  % (7036)Time limit reached!
% 4.33/0.93  % (7036)------------------------------
% 4.33/0.93  % (7036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.93  % (7036)Termination reason: Time limit
% 4.33/0.93  
% 4.33/0.93  % (7036)Memory used [KB]: 6012
% 4.33/0.93  % (7036)Time elapsed: 0.525 s
% 4.33/0.93  % (7036)------------------------------
% 4.33/0.93  % (7036)------------------------------
% 4.33/0.93  % (7147)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.68/0.98  % (7162)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.68/1.02  % (7204)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.68/1.02  % (7043)Refutation found. Thanks to Tanya!
% 4.68/1.02  % SZS status Theorem for theBenchmark
% 4.68/1.02  % SZS output start Proof for theBenchmark
% 4.68/1.02  fof(f3596,plain,(
% 4.68/1.02    $false),
% 4.68/1.02    inference(avatar_sat_refutation,[],[f121,f122,f127,f132,f137,f145,f265,f580,f671,f2028,f2311,f2334,f2475,f2488,f2500,f2518,f2538,f2543,f2636,f3476,f3558,f3595])).
% 4.68/1.02  fof(f3595,plain,(
% 4.68/1.02    sK1 != k1_tops_1(sK0,sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | v3_pre_topc(sK1,sK0)),
% 4.68/1.02    introduced(theory_tautology_sat_conflict,[])).
% 4.68/1.02  fof(f3558,plain,(
% 4.68/1.02    spl3_97 | ~spl3_3 | ~spl3_4 | ~spl3_138),
% 4.68/1.02    inference(avatar_split_clause,[],[f3557,f3473,f129,f124,f2370])).
% 4.68/1.02  fof(f2370,plain,(
% 4.68/1.02    spl3_97 <=> sK1 = k1_tops_1(sK0,sK1)),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 4.68/1.02  fof(f124,plain,(
% 4.68/1.02    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.68/1.02  fof(f129,plain,(
% 4.68/1.02    spl3_4 <=> l1_pre_topc(sK0)),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.68/1.02  fof(f3473,plain,(
% 4.68/1.02    spl3_138 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).
% 4.68/1.02  fof(f3557,plain,(
% 4.68/1.02    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_138)),
% 4.68/1.02    inference(subsumption_resolution,[],[f3556,f131])).
% 4.68/1.02  fof(f131,plain,(
% 4.68/1.02    l1_pre_topc(sK0) | ~spl3_4),
% 4.68/1.02    inference(avatar_component_clause,[],[f129])).
% 4.68/1.02  fof(f3556,plain,(
% 4.68/1.02    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_138)),
% 4.68/1.02    inference(subsumption_resolution,[],[f3535,f126])).
% 4.68/1.02  fof(f126,plain,(
% 4.68/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 4.68/1.02    inference(avatar_component_clause,[],[f124])).
% 4.68/1.02  fof(f3535,plain,(
% 4.68/1.02    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_138),
% 4.68/1.02    inference(superposition,[],[f286,f3475])).
% 4.68/1.02  fof(f3475,plain,(
% 4.68/1.02    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_138),
% 4.68/1.02    inference(avatar_component_clause,[],[f3473])).
% 4.68/1.02  fof(f286,plain,(
% 4.68/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.02    inference(duplicate_literal_removal,[],[f285])).
% 4.68/1.02  fof(f285,plain,(
% 4.68/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.02    inference(superposition,[],[f76,f87])).
% 4.68/1.02  fof(f87,plain,(
% 4.68/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.02    inference(cnf_transformation,[],[f43])).
% 4.68/1.02  fof(f43,plain,(
% 4.68/1.02    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.68/1.02    inference(ennf_transformation,[],[f32])).
% 4.68/1.02  fof(f32,axiom,(
% 4.68/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 4.68/1.02  fof(f76,plain,(
% 4.68/1.02    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.02    inference(cnf_transformation,[],[f37])).
% 4.68/1.02  fof(f37,plain,(
% 4.68/1.02    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.02    inference(ennf_transformation,[],[f22])).
% 4.68/1.02  fof(f22,axiom,(
% 4.68/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 4.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 4.68/1.02  fof(f3476,plain,(
% 4.68/1.02    spl3_76 | spl3_138 | ~spl3_23 | ~spl3_31),
% 4.68/1.02    inference(avatar_split_clause,[],[f3471,f668,f631,f3473,f1905])).
% 4.68/1.02  fof(f1905,plain,(
% 4.68/1.02    spl3_76 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 4.68/1.02  fof(f631,plain,(
% 4.68/1.02    spl3_23 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 4.68/1.02  fof(f668,plain,(
% 4.68/1.02    spl3_31 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 4.68/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 4.68/1.02  fof(f3471,plain,(
% 4.68/1.02    ( ! [X16] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_23 | ~spl3_31)),
% 4.68/1.02    inference(subsumption_resolution,[],[f3445,f633])).
% 4.68/1.02  fof(f633,plain,(
% 4.68/1.02    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_23),
% 4.68/1.02    inference(avatar_component_clause,[],[f631])).
% 4.68/1.02  fof(f3445,plain,(
% 4.68/1.02    ( ! [X16] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_31),
% 4.68/1.02    inference(superposition,[],[f780,f670])).
% 4.68/1.02  fof(f670,plain,(
% 4.68/1.02    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_31),
% 4.68/1.02    inference(avatar_component_clause,[],[f668])).
% 4.68/1.02  fof(f780,plain,(
% 4.68/1.02    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 4.68/1.02    inference(subsumption_resolution,[],[f775,f94])).
% 4.68/1.02  fof(f94,plain,(
% 4.68/1.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.02    inference(cnf_transformation,[],[f51])).
% 4.68/1.02  fof(f51,plain,(
% 4.68/1.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.02    inference(ennf_transformation,[],[f14])).
% 4.68/1.02  fof(f14,axiom,(
% 4.68/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.68/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.68/1.02  fof(f775,plain,(
% 4.68/1.02    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 4.68/1.02    inference(superposition,[],[f314,f76])).
% 4.68/1.02  fof(f314,plain,(
% 4.68/1.02    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 4.68/1.02    inference(subsumption_resolution,[],[f310,f94])).
% 4.68/1.02  fof(f310,plain,(
% 4.68/1.02    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 4.68/1.02    inference(superposition,[],[f85,f105])).
% 4.68/1.03  fof(f105,plain,(
% 4.68/1.03    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f56])).
% 4.68/1.03  fof(f56,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f18])).
% 4.68/1.03  fof(f18,axiom,(
% 4.68/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 4.68/1.03  fof(f85,plain,(
% 4.68/1.03    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f41])).
% 4.68/1.03  fof(f41,plain,(
% 4.68/1.03    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f23])).
% 4.68/1.03  fof(f23,axiom,(
% 4.68/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 4.68/1.03  fof(f2636,plain,(
% 4.68/1.03    ~spl3_76),
% 4.68/1.03    inference(avatar_contradiction_clause,[],[f2601])).
% 4.68/1.03  fof(f2601,plain,(
% 4.68/1.03    $false | ~spl3_76),
% 4.68/1.03    inference(unit_resulting_resolution,[],[f149,f95,f1906,f107])).
% 4.68/1.03  fof(f107,plain,(
% 4.68/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f60])).
% 4.68/1.03  fof(f60,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.03    inference(flattening,[],[f59])).
% 4.68/1.03  fof(f59,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.68/1.03    inference(ennf_transformation,[],[f15])).
% 4.68/1.03  fof(f15,axiom,(
% 4.68/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 4.68/1.03  fof(f1906,plain,(
% 4.68/1.03    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_76),
% 4.68/1.03    inference(avatar_component_clause,[],[f1905])).
% 4.68/1.03  fof(f95,plain,(
% 4.68/1.03    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f70])).
% 4.68/1.03  fof(f70,plain,(
% 4.68/1.03    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 4.68/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f69])).
% 4.68/1.03  fof(f69,plain,(
% 4.68/1.03    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 4.68/1.03    introduced(choice_axiom,[])).
% 4.68/1.03  fof(f17,axiom,(
% 4.68/1.03    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 4.68/1.03  fof(f149,plain,(
% 4.68/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(superposition,[],[f147,f99])).
% 4.68/1.03  fof(f99,plain,(
% 4.68/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.68/1.03    inference(cnf_transformation,[],[f7])).
% 4.68/1.03  fof(f7,axiom,(
% 4.68/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 4.68/1.03  fof(f147,plain,(
% 4.68/1.03    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(backward_demodulation,[],[f109,f98])).
% 4.68/1.03  fof(f98,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f21])).
% 4.68/1.03  fof(f21,axiom,(
% 4.68/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 4.68/1.03  fof(f109,plain,(
% 4.68/1.03    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f16])).
% 4.68/1.03  fof(f16,axiom,(
% 4.68/1.03    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 4.68/1.03  fof(f2543,plain,(
% 4.68/1.03    spl3_30 | ~spl3_75),
% 4.68/1.03    inference(avatar_contradiction_clause,[],[f2542])).
% 4.68/1.03  fof(f2542,plain,(
% 4.68/1.03    $false | (spl3_30 | ~spl3_75)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2540,f1897])).
% 4.68/1.03  fof(f1897,plain,(
% 4.68/1.03    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_75),
% 4.68/1.03    inference(avatar_component_clause,[],[f1895])).
% 4.68/1.03  fof(f1895,plain,(
% 4.68/1.03    spl3_75 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 4.68/1.03  fof(f2540,plain,(
% 4.68/1.03    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_30),
% 4.68/1.03    inference(resolution,[],[f666,f93])).
% 4.68/1.03  fof(f93,plain,(
% 4.68/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f68])).
% 4.68/1.03  fof(f68,plain,(
% 4.68/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.68/1.03    inference(nnf_transformation,[],[f25])).
% 4.68/1.03  fof(f25,axiom,(
% 4.68/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.68/1.03  fof(f666,plain,(
% 4.68/1.03    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_30),
% 4.68/1.03    inference(avatar_component_clause,[],[f664])).
% 4.68/1.03  fof(f664,plain,(
% 4.68/1.03    spl3_30 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 4.68/1.03  fof(f2538,plain,(
% 4.68/1.03    ~spl3_96 | spl3_97 | ~spl3_65),
% 4.68/1.03    inference(avatar_split_clause,[],[f2537,f1813,f2370,f2366])).
% 4.68/1.03  fof(f2366,plain,(
% 4.68/1.03    spl3_96 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 4.68/1.03  fof(f1813,plain,(
% 4.68/1.03    spl3_65 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 4.68/1.03  fof(f2537,plain,(
% 4.68/1.03    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_65),
% 4.68/1.03    inference(resolution,[],[f1814,f79])).
% 4.68/1.03  fof(f79,plain,(
% 4.68/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f67])).
% 4.68/1.03  fof(f67,plain,(
% 4.68/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.68/1.03    inference(flattening,[],[f66])).
% 4.68/1.03  fof(f66,plain,(
% 4.68/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.68/1.03    inference(nnf_transformation,[],[f2])).
% 4.68/1.03  fof(f2,axiom,(
% 4.68/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.68/1.03  fof(f1814,plain,(
% 4.68/1.03    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_65),
% 4.68/1.03    inference(avatar_component_clause,[],[f1813])).
% 4.68/1.03  fof(f2518,plain,(
% 4.68/1.03    spl3_23 | ~spl3_10),
% 4.68/1.03    inference(avatar_split_clause,[],[f2504,f239,f631])).
% 4.68/1.03  fof(f239,plain,(
% 4.68/1.03    spl3_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 4.68/1.03  fof(f2504,plain,(
% 4.68/1.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 4.68/1.03    inference(superposition,[],[f147,f241])).
% 4.68/1.03  fof(f241,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_10),
% 4.68/1.03    inference(avatar_component_clause,[],[f239])).
% 4.68/1.03  fof(f2500,plain,(
% 4.68/1.03    spl3_10 | ~spl3_2 | ~spl3_9),
% 4.68/1.03    inference(avatar_split_clause,[],[f2499,f235,f118,f239])).
% 4.68/1.03  fof(f118,plain,(
% 4.68/1.03    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.68/1.03  fof(f235,plain,(
% 4.68/1.03    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 4.68/1.03  fof(f2499,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2496,f236])).
% 4.68/1.03  fof(f236,plain,(
% 4.68/1.03    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 4.68/1.03    inference(avatar_component_clause,[],[f235])).
% 4.68/1.03  fof(f2496,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.68/1.03    inference(superposition,[],[f76,f119])).
% 4.68/1.03  fof(f119,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 4.68/1.03    inference(avatar_component_clause,[],[f118])).
% 4.68/1.03  fof(f2488,plain,(
% 4.68/1.03    ~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_97),
% 4.68/1.03    inference(avatar_contradiction_clause,[],[f2487])).
% 4.68/1.03  fof(f2487,plain,(
% 4.68/1.03    $false | (~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_97)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2486,f131])).
% 4.68/1.03  fof(f2486,plain,(
% 4.68/1.03    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10 | ~spl3_97)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2485,f126])).
% 4.68/1.03  fof(f2485,plain,(
% 4.68/1.03    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_10 | ~spl3_97)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2482,f240])).
% 4.68/1.03  fof(f240,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_10),
% 4.68/1.03    inference(avatar_component_clause,[],[f239])).
% 4.68/1.03  fof(f2482,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_97),
% 4.68/1.03    inference(superposition,[],[f927,f2372])).
% 4.68/1.03  fof(f2372,plain,(
% 4.68/1.03    sK1 = k1_tops_1(sK0,sK1) | ~spl3_97),
% 4.68/1.03    inference(avatar_component_clause,[],[f2370])).
% 4.68/1.03  fof(f927,plain,(
% 4.68/1.03    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.68/1.03    inference(subsumption_resolution,[],[f318,f307])).
% 4.68/1.03  fof(f307,plain,(
% 4.68/1.03    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.68/1.03    inference(subsumption_resolution,[],[f300,f89])).
% 4.68/1.03  fof(f89,plain,(
% 4.68/1.03    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f46])).
% 4.68/1.03  fof(f46,plain,(
% 4.68/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.68/1.03    inference(flattening,[],[f45])).
% 4.68/1.03  fof(f45,plain,(
% 4.68/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f26])).
% 4.68/1.03  fof(f26,axiom,(
% 4.68/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 4.68/1.03  fof(f300,plain,(
% 4.68/1.03    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.68/1.03    inference(duplicate_literal_removal,[],[f299])).
% 4.68/1.03  fof(f299,plain,(
% 4.68/1.03    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.68/1.03    inference(superposition,[],[f107,f88])).
% 4.68/1.03  fof(f88,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f44])).
% 4.68/1.03  fof(f44,plain,(
% 4.68/1.03    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.68/1.03    inference(ennf_transformation,[],[f31])).
% 4.68/1.03  fof(f31,axiom,(
% 4.68/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 4.68/1.03  fof(f318,plain,(
% 4.68/1.03    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.68/1.03    inference(superposition,[],[f86,f76])).
% 4.68/1.03  fof(f86,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f42])).
% 4.68/1.03  fof(f42,plain,(
% 4.68/1.03    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.68/1.03    inference(ennf_transformation,[],[f28])).
% 4.68/1.03  fof(f28,axiom,(
% 4.68/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 4.68/1.03  fof(f2475,plain,(
% 4.68/1.03    ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_96),
% 4.68/1.03    inference(avatar_contradiction_clause,[],[f2474])).
% 4.68/1.03  fof(f2474,plain,(
% 4.68/1.03    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_96)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2473,f111])).
% 4.68/1.03  fof(f111,plain,(
% 4.68/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.68/1.03    inference(equality_resolution,[],[f78])).
% 4.68/1.03  fof(f78,plain,(
% 4.68/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.68/1.03    inference(cnf_transformation,[],[f67])).
% 4.68/1.03  fof(f2473,plain,(
% 4.68/1.03    ~r1_tarski(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_96)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2465,f115])).
% 4.68/1.03  fof(f115,plain,(
% 4.68/1.03    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 4.68/1.03    inference(avatar_component_clause,[],[f114])).
% 4.68/1.03  fof(f114,plain,(
% 4.68/1.03    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.68/1.03  fof(f2465,plain,(
% 4.68/1.03    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_96)),
% 4.68/1.03    inference(resolution,[],[f2368,f342])).
% 4.68/1.03  fof(f342,plain,(
% 4.68/1.03    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 4.68/1.03    inference(subsumption_resolution,[],[f334,f191])).
% 4.68/1.03  fof(f191,plain,(
% 4.68/1.03    ( ! [X11] : (r1_tarski(X11,u1_struct_0(sK0)) | ~r1_tarski(X11,sK1)) ) | ~spl3_6),
% 4.68/1.03    inference(resolution,[],[f100,f144])).
% 4.68/1.03  fof(f144,plain,(
% 4.68/1.03    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 4.68/1.03    inference(avatar_component_clause,[],[f142])).
% 4.68/1.03  fof(f142,plain,(
% 4.68/1.03    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 4.68/1.03  fof(f100,plain,(
% 4.68/1.03    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f55])).
% 4.68/1.03  fof(f55,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.68/1.03    inference(flattening,[],[f54])).
% 4.68/1.03  fof(f54,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.68/1.03    inference(ennf_transformation,[],[f4])).
% 4.68/1.03  fof(f4,axiom,(
% 4.68/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.68/1.03  fof(f334,plain,(
% 4.68/1.03    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_4)),
% 4.68/1.03    inference(resolution,[],[f333,f93])).
% 4.68/1.03  fof(f333,plain,(
% 4.68/1.03    ( ! [X18] : (~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~r1_tarski(X18,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 4.68/1.03    inference(subsumption_resolution,[],[f329,f131])).
% 4.68/1.03  fof(f329,plain,(
% 4.68/1.03    ( ! [X18] : (~r1_tarski(X18,sK1) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 4.68/1.03    inference(resolution,[],[f91,f126])).
% 4.68/1.03  fof(f91,plain,(
% 4.68/1.03    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f50])).
% 4.68/1.03  fof(f50,plain,(
% 4.68/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.68/1.03    inference(flattening,[],[f49])).
% 4.68/1.03  fof(f49,plain,(
% 4.68/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.68/1.03    inference(ennf_transformation,[],[f29])).
% 4.68/1.03  fof(f29,axiom,(
% 4.68/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 4.68/1.03  fof(f2368,plain,(
% 4.68/1.03    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_96),
% 4.68/1.03    inference(avatar_component_clause,[],[f2366])).
% 4.68/1.03  fof(f2334,plain,(
% 4.68/1.03    spl3_75 | ~spl3_3 | ~spl3_4),
% 4.68/1.03    inference(avatar_split_clause,[],[f2333,f129,f124,f1895])).
% 4.68/1.03  fof(f2333,plain,(
% 4.68/1.03    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2323,f131])).
% 4.68/1.03  fof(f2323,plain,(
% 4.68/1.03    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.68/1.03    inference(resolution,[],[f704,f126])).
% 4.68/1.03  fof(f704,plain,(
% 4.68/1.03    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(X3,k2_pre_topc(X4,X3)) | ~l1_pre_topc(X4)) )),
% 4.68/1.03    inference(superposition,[],[f101,f305])).
% 4.68/1.03  fof(f305,plain,(
% 4.68/1.03    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.68/1.03    inference(subsumption_resolution,[],[f302,f89])).
% 4.68/1.03  fof(f302,plain,(
% 4.68/1.03    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.68/1.03    inference(duplicate_literal_removal,[],[f297])).
% 4.68/1.03  fof(f297,plain,(
% 4.68/1.03    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.68/1.03    inference(superposition,[],[f88,f106])).
% 4.68/1.03  fof(f106,plain,(
% 4.68/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f58])).
% 4.68/1.03  fof(f58,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.03    inference(flattening,[],[f57])).
% 4.68/1.03  fof(f57,plain,(
% 4.68/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.68/1.03    inference(ennf_transformation,[],[f20])).
% 4.68/1.03  fof(f20,axiom,(
% 4.68/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.68/1.03  fof(f101,plain,(
% 4.68/1.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f11])).
% 4.68/1.03  fof(f11,axiom,(
% 4.68/1.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.68/1.03  fof(f2311,plain,(
% 4.68/1.03    spl3_65 | ~spl3_3 | ~spl3_4),
% 4.68/1.03    inference(avatar_split_clause,[],[f2310,f129,f124,f1813])).
% 4.68/1.03  fof(f2310,plain,(
% 4.68/1.03    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 4.68/1.03    inference(subsumption_resolution,[],[f2300,f131])).
% 4.68/1.03  fof(f2300,plain,(
% 4.68/1.03    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.68/1.03    inference(resolution,[],[f681,f126])).
% 4.68/1.03  fof(f681,plain,(
% 4.68/1.03    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(k1_tops_1(X7,X6),X6) | ~l1_pre_topc(X7)) )),
% 4.68/1.03    inference(superposition,[],[f148,f286])).
% 4.68/1.03  fof(f148,plain,(
% 4.68/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.68/1.03    inference(resolution,[],[f147,f92])).
% 4.68/1.03  fof(f92,plain,(
% 4.68/1.03    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f68])).
% 4.68/1.03  fof(f2028,plain,(
% 4.68/1.03    ~spl3_9 | ~spl3_10 | spl3_2),
% 4.68/1.03    inference(avatar_split_clause,[],[f2027,f118,f239,f235])).
% 4.68/1.03  fof(f2027,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 4.68/1.03    inference(superposition,[],[f120,f76])).
% 4.68/1.03  fof(f120,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 4.68/1.03    inference(avatar_component_clause,[],[f118])).
% 4.68/1.03  fof(f671,plain,(
% 4.68/1.03    ~spl3_30 | spl3_31 | ~spl3_10),
% 4.68/1.03    inference(avatar_split_clause,[],[f615,f239,f668,f664])).
% 4.68/1.03  fof(f615,plain,(
% 4.68/1.03    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 4.68/1.03    inference(superposition,[],[f222,f241])).
% 4.68/1.03  fof(f222,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(duplicate_literal_removal,[],[f218])).
% 4.68/1.03  fof(f218,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(superposition,[],[f80,f81])).
% 4.68/1.03  fof(f81,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f39])).
% 4.68/1.03  fof(f39,plain,(
% 4.68/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f13])).
% 4.68/1.03  fof(f13,axiom,(
% 4.68/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 4.68/1.03  fof(f80,plain,(
% 4.68/1.03    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.68/1.03    inference(cnf_transformation,[],[f38])).
% 4.68/1.03  fof(f38,plain,(
% 4.68/1.03    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f19])).
% 4.68/1.03  fof(f19,axiom,(
% 4.68/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 4.68/1.03  fof(f580,plain,(
% 4.68/1.03    ~spl3_3 | ~spl3_4 | spl3_9),
% 4.68/1.03    inference(avatar_contradiction_clause,[],[f579])).
% 4.68/1.03  fof(f579,plain,(
% 4.68/1.03    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 4.68/1.03    inference(subsumption_resolution,[],[f578,f131])).
% 4.68/1.03  fof(f578,plain,(
% 4.68/1.03    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 4.68/1.03    inference(subsumption_resolution,[],[f571,f126])).
% 4.68/1.03  fof(f571,plain,(
% 4.68/1.03    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 4.68/1.03    inference(resolution,[],[f307,f237])).
% 4.68/1.03  fof(f237,plain,(
% 4.68/1.03    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 4.68/1.03    inference(avatar_component_clause,[],[f235])).
% 4.68/1.03  fof(f265,plain,(
% 4.68/1.03    spl3_12 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 4.68/1.03    inference(avatar_split_clause,[],[f260,f134,f129,f124,f262])).
% 4.68/1.03  fof(f262,plain,(
% 4.68/1.03    spl3_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 4.68/1.03  fof(f134,plain,(
% 4.68/1.03    spl3_5 <=> v2_pre_topc(sK0)),
% 4.68/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.68/1.03  fof(f260,plain,(
% 4.68/1.03    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 4.68/1.03    inference(subsumption_resolution,[],[f259,f136])).
% 4.68/1.03  fof(f136,plain,(
% 4.68/1.03    v2_pre_topc(sK0) | ~spl3_5),
% 4.68/1.03    inference(avatar_component_clause,[],[f134])).
% 4.68/1.03  fof(f259,plain,(
% 4.68/1.03    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 4.68/1.03    inference(subsumption_resolution,[],[f256,f131])).
% 4.68/1.03  fof(f256,plain,(
% 4.68/1.03    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 4.68/1.03    inference(resolution,[],[f90,f126])).
% 4.68/1.03  fof(f90,plain,(
% 4.68/1.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.68/1.03    inference(cnf_transformation,[],[f48])).
% 4.68/1.03  fof(f48,plain,(
% 4.68/1.03    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.68/1.03    inference(flattening,[],[f47])).
% 4.68/1.03  fof(f47,plain,(
% 4.68/1.03    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f27])).
% 4.68/1.03  fof(f27,axiom,(
% 4.68/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 4.68/1.03  fof(f145,plain,(
% 4.68/1.03    spl3_6 | ~spl3_3),
% 4.68/1.03    inference(avatar_split_clause,[],[f138,f124,f142])).
% 4.68/1.03  fof(f138,plain,(
% 4.68/1.03    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 4.68/1.03    inference(resolution,[],[f92,f126])).
% 4.68/1.03  fof(f137,plain,(
% 4.68/1.03    spl3_5),
% 4.68/1.03    inference(avatar_split_clause,[],[f71,f134])).
% 4.68/1.03  fof(f71,plain,(
% 4.68/1.03    v2_pre_topc(sK0)),
% 4.68/1.03    inference(cnf_transformation,[],[f65])).
% 4.68/1.03  fof(f65,plain,(
% 4.68/1.03    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.68/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).
% 4.68/1.03  fof(f63,plain,(
% 4.68/1.03    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.68/1.03    introduced(choice_axiom,[])).
% 4.68/1.03  fof(f64,plain,(
% 4.68/1.03    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.68/1.03    introduced(choice_axiom,[])).
% 4.68/1.03  fof(f62,plain,(
% 4.68/1.03    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.68/1.03    inference(flattening,[],[f61])).
% 4.68/1.03  fof(f61,plain,(
% 4.68/1.03    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.68/1.03    inference(nnf_transformation,[],[f36])).
% 4.68/1.03  fof(f36,plain,(
% 4.68/1.03    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.68/1.03    inference(flattening,[],[f35])).
% 4.68/1.03  fof(f35,plain,(
% 4.68/1.03    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.68/1.03    inference(ennf_transformation,[],[f34])).
% 4.68/1.03  fof(f34,negated_conjecture,(
% 4.68/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.68/1.03    inference(negated_conjecture,[],[f33])).
% 4.68/1.03  fof(f33,conjecture,(
% 4.68/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.68/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 4.68/1.03  fof(f132,plain,(
% 4.68/1.03    spl3_4),
% 4.68/1.03    inference(avatar_split_clause,[],[f72,f129])).
% 4.68/1.03  fof(f72,plain,(
% 4.68/1.03    l1_pre_topc(sK0)),
% 4.68/1.03    inference(cnf_transformation,[],[f65])).
% 4.68/1.03  fof(f127,plain,(
% 4.68/1.03    spl3_3),
% 4.68/1.03    inference(avatar_split_clause,[],[f73,f124])).
% 4.68/1.03  fof(f73,plain,(
% 4.68/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.68/1.03    inference(cnf_transformation,[],[f65])).
% 4.68/1.03  fof(f122,plain,(
% 4.68/1.03    spl3_1 | spl3_2),
% 4.68/1.03    inference(avatar_split_clause,[],[f74,f118,f114])).
% 4.68/1.03  fof(f74,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 4.68/1.03    inference(cnf_transformation,[],[f65])).
% 4.68/1.03  fof(f121,plain,(
% 4.68/1.03    ~spl3_1 | ~spl3_2),
% 4.68/1.03    inference(avatar_split_clause,[],[f75,f118,f114])).
% 4.68/1.03  fof(f75,plain,(
% 4.68/1.03    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 4.68/1.03    inference(cnf_transformation,[],[f65])).
% 4.68/1.03  % SZS output end Proof for theBenchmark
% 4.68/1.03  % (7043)------------------------------
% 4.68/1.03  % (7043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.03  % (7043)Termination reason: Refutation
% 4.68/1.03  
% 4.68/1.03  % (7043)Memory used [KB]: 10490
% 4.68/1.03  % (7043)Time elapsed: 0.586 s
% 4.68/1.03  % (7043)------------------------------
% 4.68/1.03  % (7043)------------------------------
% 4.68/1.03  % (7021)Success in time 0.669 s
%------------------------------------------------------------------------------
