%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:06 EST 2020

% Result     : Theorem 4.08s
% Output     : Refutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  359 (1319 expanded)
%              Number of leaves         :   87 ( 549 expanded)
%              Depth                    :   10
%              Number of atoms          :  917 (3014 expanded)
%              Number of equality atoms :  119 ( 491 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3523,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f63,f74,f81,f106,f125,f130,f152,f157,f169,f296,f301,f306,f311,f316,f324,f350,f381,f389,f458,f465,f504,f516,f521,f541,f553,f608,f667,f726,f770,f775,f827,f838,f843,f848,f853,f858,f863,f873,f1165,f1170,f1175,f1180,f1185,f1244,f1249,f1326,f1564,f1569,f1940,f1945,f2073,f2075,f2233,f2258,f2263,f2268,f2273,f2278,f2283,f2288,f2289,f2303,f2308,f2732,f2746,f2751,f3209,f3456,f3461,f3466,f3471,f3476,f3481,f3486,f3492,f3513,f3522])).

fof(f3522,plain,
    ( ~ spl3_37
    | ~ spl3_38
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f3521])).

fof(f3521,plain,
    ( $false
    | ~ spl3_37
    | ~ spl3_38
    | spl3_52 ),
    inference(subsumption_resolution,[],[f3520,f866])).

fof(f866,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f837,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f837,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f835])).

fof(f835,plain,
    ( spl3_37
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f3520,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ spl3_38
    | spl3_52 ),
    inference(subsumption_resolution,[],[f3519,f876])).

fof(f876,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f842,f31])).

fof(f842,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f840])).

fof(f840,plain,
    ( spl3_38
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f3519,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_52 ),
    inference(resolution,[],[f1563,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f34,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1563,plain,
    ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f1561])).

fof(f1561,plain,
    ( spl3_52
  <=> m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f3513,plain,
    ( spl3_77
    | ~ spl3_3
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f1494,f824,f47,f3510])).

fof(f3510,plain,
    ( spl3_77
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f47,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f824,plain,
    ( spl3_36
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1494,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl3_3
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f1455,f826])).

fof(f826,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f824])).

fof(f1455,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f49,f49,f365])).

fof(f365,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X0,k4_subset_1(X0,X1,X2)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f357,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f357,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_subset_1(X0,X1,X2),X0) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k2_xboole_0(X2,X3) = X3 ) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f49,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f3492,plain,
    ( spl3_76
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f814,f664,f149,f37,f3489])).

fof(f3489,plain,
    ( spl3_76
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f37,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( spl3_10
  <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f664,plain,
    ( spl3_32
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f814,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f701,f792])).

fof(f792,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f666,f30])).

fof(f666,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f664])).

fof(f701,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_xboole_0(sK1,sK1)),k1_tops_1(sK0,k2_xboole_0(sK1,sK1)))
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f39,f151,f151,f343,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f343,plain,(
    ! [X8,X9] : r1_tarski(k2_xboole_0(X8,X9),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f51,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f28,f29])).

fof(f151,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f39,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f3486,plain,
    ( spl3_75
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2204,f451,f47,f3483])).

fof(f3483,plain,
    ( spl3_75
  <=> k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f451,plain,
    ( spl3_23
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f2204,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f2113,f29])).

fof(f2113,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK1) = k2_xboole_0(k1_tops_1(sK0,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f49,f452,f35])).

fof(f452,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f451])).

fof(f3481,plain,
    ( spl3_74
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f2191,f767,f451,f3478])).

fof(f3478,plain,
    ( spl3_74
  <=> k1_tops_1(sK0,sK2) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f767,plain,
    ( spl3_34
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f2191,plain,
    ( k1_tops_1(sK0,sK2) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f2118,f777])).

fof(f777,plain,
    ( k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f769,f30])).

fof(f769,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f767])).

fof(f2118,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f452,f452,f35])).

fof(f3476,plain,
    ( spl3_73
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2119,f451,f47,f3473])).

fof(f3473,plain,
    ( spl3_73
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f2119,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f49,f452,f35])).

fof(f3471,plain,
    ( spl3_72
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f592,f550,f3468])).

fof(f3468,plain,
    ( spl3_72
  <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f550,plain,
    ( spl3_30
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f592,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_30 ),
    inference(superposition,[],[f552,f29])).

fof(f552,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f550])).

fof(f3466,plain,
    ( spl3_71
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f2048,f447,f42,f3463])).

fof(f3463,plain,
    ( spl3_71
  <=> k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f42,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f447,plain,
    ( spl3_22
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f2048,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f1973,f29])).

fof(f1973,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK2) = k2_xboole_0(k1_tops_1(sK0,sK1),sK2)
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f44,f448,f35])).

fof(f448,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f447])).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f3461,plain,
    ( spl3_70
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f2041,f664,f447,f47,f37,f3458])).

fof(f3458,plain,
    ( spl3_70
  <=> k1_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f2041,plain,
    ( k1_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f1976,f1547])).

fof(f1547,plain,
    ( k1_tops_1(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f666,f49,f49,f445])).

fof(f445,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X4,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X3) = k2_xboole_0(k1_tops_1(sK0,X4),k1_tops_1(sK0,X3)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f115,f30])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f27,f39])).

fof(f1976,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f448,f448,f35])).

fof(f3456,plain,
    ( spl3_69
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1978,f447,f42,f3453])).

fof(f3453,plain,
    ( spl3_69
  <=> k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f1978,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f44,f448,f35])).

fof(f3209,plain,
    ( spl3_68
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f580,f538,f3206])).

fof(f3206,plain,
    ( spl3_68
  <=> sK2 = k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f538,plain,
    ( spl3_29
  <=> sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f580,plain,
    ( sK2 = k2_xboole_0(sK2,k1_tops_1(sK0,sK2))
    | ~ spl3_29 ),
    inference(superposition,[],[f540,f29])).

fof(f540,plain,
    ( sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f538])).

fof(f2751,plain,
    ( spl3_67
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2131,f451,f447,f2748])).

fof(f2748,plain,
    ( spl3_67
  <=> m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f2131,plain,
    ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f448,f452,f93])).

fof(f2746,plain,
    ( spl3_66
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2129,f451,f154,f2743])).

fof(f2743,plain,
    ( spl3_66
  <=> m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f154,plain,
    ( spl3_11
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f2129,plain,
    ( m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f156,f452,f93])).

fof(f156,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f2732,plain,
    ( spl3_65
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1986,f447,f154,f2729])).

fof(f2729,plain,
    ( spl3_65
  <=> m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1986,plain,
    ( m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f156,f448,f93])).

fof(f2308,plain,
    ( spl3_64
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f2202,f538,f451,f42,f2305])).

fof(f2305,plain,
    ( spl3_64
  <=> sK2 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f2202,plain,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f2201,f580])).

fof(f2201,plain,
    ( k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f2114,f29])).

fof(f2114,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f44,f452,f35])).

fof(f2303,plain,
    ( spl3_63
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f2188,f538,f451,f42,f2300])).

fof(f2300,plain,
    ( spl3_63
  <=> sK2 = k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f2188,plain,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f2120,f580])).

fof(f2120,plain,
    ( k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f44,f452,f35])).

fof(f2289,plain,
    ( spl3_26
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1932,f518,f127,f501])).

fof(f501,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f127,plain,
    ( spl3_9
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f518,plain,
    ( spl3_28
  <=> u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1932,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(superposition,[],[f547,f520])).

fof(f520,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f518])).

fof(f547,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X0))
    | ~ spl3_9 ),
    inference(superposition,[],[f136,f29])).

fof(f136,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f129,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f129,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f2288,plain,
    ( spl3_62
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2133,f451,f47,f2285])).

fof(f2285,plain,
    ( spl3_62
  <=> m1_subset_1(k2_xboole_0(sK1,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f2133,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f49,f452,f93])).

fof(f2283,plain,
    ( spl3_61
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2095,f451,f37,f2280])).

fof(f2280,plain,
    ( spl3_61
  <=> r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f2095,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f39,f452,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2278,plain,
    ( spl3_60
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f2051,f550,f447,f47,f2275])).

fof(f2275,plain,
    ( spl3_60
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f2051,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f2050,f592])).

fof(f2050,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f1972,f29])).

fof(f1972,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f49,f448,f35])).

fof(f2273,plain,
    ( spl3_59
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f2039,f550,f447,f47,f2270])).

fof(f2270,plain,
    ( spl3_59
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f2039,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1977,f592])).

fof(f1977,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f49,f448,f35])).

fof(f2268,plain,
    ( spl3_58
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f1920,f513,f122,f2265])).

fof(f2265,plain,
    ( spl3_58
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f122,plain,
    ( spl3_8
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f513,plain,
    ( spl3_27
  <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1920,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(superposition,[],[f535,f515])).

fof(f515,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f513])).

fof(f535,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(sK2,X0))
    | ~ spl3_8 ),
    inference(superposition,[],[f131,f29])).

fof(f131,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2))
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f124,f33])).

fof(f124,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f2263,plain,
    ( spl3_57
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1990,f447,f42,f2260])).

fof(f2260,plain,
    ( spl3_57
  <=> m1_subset_1(k2_xboole_0(sK2,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1990,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f44,f448,f93])).

fof(f2258,plain,
    ( spl3_56
    | ~ spl3_1
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1957,f447,f37,f2255])).

fof(f2255,plain,
    ( spl3_56
  <=> r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f1957,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f39,f448,f26])).

fof(f2233,plain,
    ( spl3_55
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f1129,f870,f664,f2230])).

fof(f2230,plain,
    ( spl3_55
  <=> sK1 = k4_subset_1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f870,plain,
    ( spl3_43
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1129,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f1116,f792])).

fof(f1116,plain,
    ( k2_xboole_0(sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl3_43 ),
    inference(unit_resulting_resolution,[],[f872,f872,f35])).

fof(f872,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f870])).

fof(f2075,plain,
    ( ~ spl3_8
    | spl3_23
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f2074])).

fof(f2074,plain,
    ( $false
    | ~ spl3_8
    | spl3_23
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f2071,f1920])).

fof(f2071,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_23 ),
    inference(resolution,[],[f453,f31])).

fof(f453,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f451])).

fof(f2073,plain,
    ( ~ spl3_8
    | spl3_23
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f2072])).

fof(f2072,plain,
    ( $false
    | ~ spl3_8
    | spl3_23
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f2070,f1920])).

fof(f2070,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f453,f31])).

fof(f1945,plain,
    ( spl3_54
    | ~ spl3_31
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f941,f845,f605,f1942])).

fof(f1942,plain,
    ( spl3_54
  <=> sK2 = k4_subset_1(sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f605,plain,
    ( spl3_31
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f845,plain,
    ( spl3_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f941,plain,
    ( sK2 = k4_subset_1(sK2,sK2,sK2)
    | ~ spl3_31
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f928,f730])).

fof(f730,plain,
    ( sK2 = k2_xboole_0(sK2,sK2)
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f607,f30])).

fof(f607,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f605])).

fof(f928,plain,
    ( k2_xboole_0(sK2,sK2) = k4_subset_1(sK2,sK2,sK2)
    | ~ spl3_39 ),
    inference(unit_resulting_resolution,[],[f847,f847,f35])).

fof(f847,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f845])).

fof(f1940,plain,
    ( ~ spl3_9
    | spl3_26
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f1939])).

fof(f1939,plain,
    ( $false
    | ~ spl3_9
    | spl3_26
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1932,f503])).

fof(f503,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f501])).

fof(f1569,plain,
    ( spl3_53
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f630,f518,f1566])).

fof(f1566,plain,
    ( spl3_53
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f630,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_28 ),
    inference(superposition,[],[f143,f520])).

fof(f143,plain,(
    ! [X0,X1] : m1_subset_1(X0,k1_zfmisc_1(k2_xboole_0(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f51,f31])).

fof(f1564,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | ~ spl3_52
    | spl3_20 ),
    inference(avatar_split_clause,[],[f384,f378,f1561,f451,f447])).

fof(f378,plain,
    ( spl3_20
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f384,plain,
    ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(superposition,[],[f380,f35])).

fof(f380,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1326,plain,
    ( spl3_51
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f792,f664,f1323])).

fof(f1323,plain,
    ( spl3_51
  <=> sK1 = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f1249,plain,
    ( spl3_50
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f719,f154,f1246])).

fof(f1246,plain,
    ( spl3_50
  <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f719,plain,
    ( k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f205,f705])).

fof(f705,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f343,f30])).

fof(f205,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f156,f156,f35])).

fof(f1244,plain,
    ( spl3_49
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f730,f605,f1241])).

fof(f1241,plain,
    ( spl3_49
  <=> sK2 = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1185,plain,
    ( spl3_48
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f227,f154,f42,f1182])).

fof(f1182,plain,
    ( spl3_48
  <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f227,plain,
    ( k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f226,f142])).

fof(f142,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f51,f30])).

fof(f226,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f198,f29])).

fof(f198,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f44,f156,f35])).

fof(f1180,plain,
    ( spl3_47
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f565,f513,f1177])).

fof(f1177,plain,
    ( spl3_47
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f565,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl3_27 ),
    inference(superposition,[],[f51,f515])).

fof(f1175,plain,
    ( spl3_46
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f224,f154,f47,f1172])).

fof(f1172,plain,
    ( spl3_46
  <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f224,plain,
    ( k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f223,f56])).

fof(f223,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f199,f29])).

fof(f199,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f49,f156,f35])).

fof(f1170,plain,
    ( spl3_45
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f219,f154,f42,f1167])).

fof(f1167,plain,
    ( spl3_45
  <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f219,plain,
    ( k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f202,f142])).

fof(f202,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f44,f156,f35])).

fof(f1165,plain,
    ( spl3_44
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f217,f154,f47,f1162])).

fof(f1162,plain,
    ( spl3_44
  <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f217,plain,
    ( k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f203,f56])).

fof(f203,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f49,f156,f35])).

fof(f873,plain,
    ( spl3_43
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f629,f550,f870])).

fof(f629,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_30 ),
    inference(superposition,[],[f143,f552])).

fof(f863,plain,
    ( spl3_42
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f764,f605,f166,f154,f42,f860])).

fof(f860,plain,
    ( spl3_42
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f166,plain,
    ( spl3_12
  <=> m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f764,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f744,f219])).

fof(f744,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f259,f730])).

fof(f259,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK2))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f235,f29])).

fof(f235,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f156,f168,f35])).

fof(f168,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f858,plain,
    ( spl3_41
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f354,f154,f855])).

fof(f855,plain,
    ( spl3_41
  <=> u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f354,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f156,f58])).

fof(f853,plain,
    ( spl3_40
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f197,f154,f37,f850])).

fof(f850,plain,
    ( spl3_40
  <=> r1_tarski(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f197,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f39,f156,f26])).

fof(f848,plain,
    ( spl3_39
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f628,f538,f845])).

fof(f628,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl3_29 ),
    inference(superposition,[],[f143,f540])).

fof(f843,plain,
    ( spl3_38
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f196,f154,f42,f37,f840])).

fof(f196,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f39,f44,f51,f156,f27])).

fof(f838,plain,
    ( spl3_37
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f195,f154,f47,f37,f835])).

fof(f195,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f39,f49,f28,f156,f27])).

fof(f827,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f799,f664,f149,f47,f824])).

fof(f799,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f187,f792])).

fof(f187,plain,
    ( k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f177,f56])).

fof(f177,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f49,f151,f35])).

fof(f775,plain,
    ( spl3_35
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f743,f605,f166,f42,f772])).

fof(f772,plain,
    ( spl3_35
  <=> sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f743,plain,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f257,f730])).

fof(f257,plain,
    ( k2_xboole_0(sK2,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK2))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f237,f56])).

fof(f237,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK2,sK2))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f44,f168,f35])).

fof(f770,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f735,f605,f166,f42,f37,f767])).

fof(f735,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f230,f730])).

fof(f230,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f39,f44,f51,f168,f27])).

fof(f726,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f171,f149,f47,f37,f723])).

fof(f723,plain,
    ( spl3_33
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f171,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK1)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f39,f49,f51,f151,f27])).

fof(f667,plain,
    ( spl3_32
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f598,f550,f664])).

fof(f598,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_30 ),
    inference(superposition,[],[f51,f552])).

fof(f608,plain,
    ( spl3_31
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f586,f538,f605])).

fof(f586,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl3_29 ),
    inference(superposition,[],[f51,f540])).

fof(f553,plain,
    ( spl3_30
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f137,f127,f550])).

fof(f137,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f129,f30])).

fof(f541,plain,
    ( spl3_29
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f132,f122,f538])).

fof(f132,plain,
    ( sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f124,f30])).

fof(f521,plain,
    ( spl3_28
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f117,f78,f518])).

fof(f78,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f80,f30])).

fof(f80,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f516,plain,
    ( spl3_27
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f60,f513])).

fof(f60,plain,
    ( spl3_4
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f111,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f62,f30])).

fof(f62,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f504,plain,
    ( ~ spl3_26
    | spl3_22 ),
    inference(avatar_split_clause,[],[f459,f447,f501])).

fof(f459,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f449,f31])).

fof(f449,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f447])).

fof(f465,plain,
    ( spl3_25
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f252,f166,f462])).

fof(f462,plain,
    ( spl3_25
  <=> r1_tarski(k2_xboole_0(sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f252,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK2),u1_struct_0(sK0))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f168,f32])).

fof(f458,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f101,f71,f47,f42,f455,f451,f447])).

fof(f455,plain,
    ( spl3_24
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f71,plain,
    ( spl3_5
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5 ),
    inference(forward_demodulation,[],[f90,f87])).

fof(f87,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f49,f44,f35])).

fof(f90,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(superposition,[],[f73,f35])).

fof(f73,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f389,plain,
    ( spl3_21
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f214,f154,f386])).

fof(f386,plain,
    ( spl3_21
  <=> r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f214,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f156,f32])).

fof(f381,plain,
    ( ~ spl3_20
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f98,f71,f47,f42,f378])).

fof(f98,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5 ),
    inference(backward_demodulation,[],[f75,f87])).

fof(f75,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f73,f32])).

fof(f350,plain,
    ( spl3_19
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f185,f149,f347])).

fof(f347,plain,
    ( spl3_19
  <=> r1_tarski(k2_xboole_0(sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f185,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f151,f32])).

fof(f324,plain,
    ( spl3_18
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f138,f127,f321])).

fof(f321,plain,
    ( spl3_18
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f138,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f129,f31])).

fof(f316,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f95,f47,f42,f313])).

fof(f313,plain,
    ( spl3_17
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f95,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f88,f29])).

fof(f88,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f44,f49,f35])).

fof(f311,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f89,f47,f308])).

fof(f308,plain,
    ( spl3_16
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f89,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f49,f49,f35])).

fof(f306,plain,
    ( spl3_15
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f133,f122,f303])).

fof(f303,plain,
    ( spl3_15
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f133,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f124,f31])).

fof(f301,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f87,f47,f42,f298])).

fof(f298,plain,
    ( spl3_14
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f296,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f86,f42,f293])).

fof(f293,plain,
    ( spl3_13
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f86,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f44,f44,f35])).

fof(f169,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f100,f42,f166])).

fof(f100,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f82,f86])).

fof(f82,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f44,f44,f34])).

fof(f157,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f96,f47,f42,f154])).

fof(f96,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f84,f95])).

fof(f84,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f44,f49,f34])).

fof(f152,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f94,f47,f149])).

fof(f94,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f85,f89])).

fof(f85,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f49,f49,f34])).

fof(f130,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f68,f47,f37,f127])).

fof(f68,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f39,f49,f26])).

fof(f125,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f67,f42,f37,f122])).

fof(f67,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f39,f44,f26])).

fof(f106,plain,
    ( ~ spl3_7
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f99,f71,f47,f42,f103])).

fof(f103,plain,
    ( spl3_7
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5 ),
    inference(backward_demodulation,[],[f73,f87])).

fof(f81,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f47,f78])).

fof(f55,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f49,f32])).

fof(f74,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f23,f71])).

fof(f23,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f63,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f42,f60])).

fof(f54,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f44,f32])).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:45:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (4917)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.48  % (4913)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (4910)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (4921)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.48  % (4900)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (4920)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (4901)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (4902)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (4902)Refutation not found, incomplete strategy% (4902)------------------------------
% 0.21/0.50  % (4902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4922)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (4908)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (4911)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (4902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4902)Memory used [KB]: 10490
% 0.21/0.50  % (4902)Time elapsed: 0.092 s
% 0.21/0.50  % (4902)------------------------------
% 0.21/0.50  % (4902)------------------------------
% 0.21/0.50  % (4903)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (4898)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (4914)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (4923)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (4923)Refutation not found, incomplete strategy% (4923)------------------------------
% 0.21/0.51  % (4923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4912)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (4905)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (4915)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (4907)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (4918)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (4906)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (4919)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (4909)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (4923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4923)Memory used [KB]: 10618
% 0.21/0.52  % (4923)Time elapsed: 0.057 s
% 0.21/0.52  % (4923)------------------------------
% 0.21/0.52  % (4923)------------------------------
% 0.21/0.53  % (4916)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 2.21/0.63  % (4922)Refutation not found, incomplete strategy% (4922)------------------------------
% 2.21/0.63  % (4922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.63  % (4922)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.63  
% 2.21/0.63  % (4922)Memory used [KB]: 1663
% 2.21/0.63  % (4922)Time elapsed: 0.195 s
% 2.21/0.63  % (4922)------------------------------
% 2.21/0.63  % (4922)------------------------------
% 4.08/0.88  % (4915)Refutation found. Thanks to Tanya!
% 4.08/0.88  % SZS status Theorem for theBenchmark
% 4.08/0.90  % SZS output start Proof for theBenchmark
% 4.08/0.90  fof(f3523,plain,(
% 4.08/0.90    $false),
% 4.08/0.90    inference(avatar_sat_refutation,[],[f40,f45,f50,f63,f74,f81,f106,f125,f130,f152,f157,f169,f296,f301,f306,f311,f316,f324,f350,f381,f389,f458,f465,f504,f516,f521,f541,f553,f608,f667,f726,f770,f775,f827,f838,f843,f848,f853,f858,f863,f873,f1165,f1170,f1175,f1180,f1185,f1244,f1249,f1326,f1564,f1569,f1940,f1945,f2073,f2075,f2233,f2258,f2263,f2268,f2273,f2278,f2283,f2288,f2289,f2303,f2308,f2732,f2746,f2751,f3209,f3456,f3461,f3466,f3471,f3476,f3481,f3486,f3492,f3513,f3522])).
% 4.08/0.90  fof(f3522,plain,(
% 4.08/0.90    ~spl3_37 | ~spl3_38 | spl3_52),
% 4.08/0.90    inference(avatar_contradiction_clause,[],[f3521])).
% 4.08/0.90  fof(f3521,plain,(
% 4.08/0.90    $false | (~spl3_37 | ~spl3_38 | spl3_52)),
% 4.08/0.90    inference(subsumption_resolution,[],[f3520,f866])).
% 4.08/0.90  fof(f866,plain,(
% 4.08/0.90    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~spl3_37),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f837,f31])).
% 4.08/0.90  fof(f31,plain,(
% 4.08/0.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f7])).
% 4.08/0.90  fof(f7,axiom,(
% 4.08/0.90    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 4.08/0.90  fof(f837,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_37),
% 4.08/0.90    inference(avatar_component_clause,[],[f835])).
% 4.08/0.90  fof(f835,plain,(
% 4.08/0.90    spl3_37 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 4.08/0.90  fof(f3520,plain,(
% 4.08/0.90    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | (~spl3_38 | spl3_52)),
% 4.08/0.90    inference(subsumption_resolution,[],[f3519,f876])).
% 4.08/0.90  fof(f876,plain,(
% 4.08/0.90    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~spl3_38),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f842,f31])).
% 4.08/0.90  fof(f842,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_38),
% 4.08/0.90    inference(avatar_component_clause,[],[f840])).
% 4.08/0.90  fof(f840,plain,(
% 4.08/0.90    spl3_38 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 4.08/0.90  fof(f3519,plain,(
% 4.08/0.90    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_52),
% 4.08/0.90    inference(resolution,[],[f1563,f93])).
% 4.08/0.90  fof(f93,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.90    inference(duplicate_literal_removal,[],[f92])).
% 4.08/0.90  fof(f92,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.90    inference(superposition,[],[f34,f35])).
% 4.08/0.90  fof(f35,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f21])).
% 4.08/0.90  fof(f21,plain,(
% 4.08/0.90    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.08/0.90    inference(flattening,[],[f20])).
% 4.08/0.90  fof(f20,plain,(
% 4.08/0.90    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.08/0.90    inference(ennf_transformation,[],[f6])).
% 4.08/0.90  fof(f6,axiom,(
% 4.08/0.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.08/0.90  fof(f34,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f19])).
% 4.08/0.90  fof(f19,plain,(
% 4.08/0.90    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.08/0.90    inference(flattening,[],[f18])).
% 4.08/0.90  fof(f18,plain,(
% 4.08/0.90    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.08/0.90    inference(ennf_transformation,[],[f5])).
% 4.08/0.90  fof(f5,axiom,(
% 4.08/0.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 4.08/0.90  fof(f1563,plain,(
% 4.08/0.90    ~m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_52),
% 4.08/0.90    inference(avatar_component_clause,[],[f1561])).
% 4.08/0.90  fof(f1561,plain,(
% 4.08/0.90    spl3_52 <=> m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 4.08/0.90  fof(f3513,plain,(
% 4.08/0.90    spl3_77 | ~spl3_3 | ~spl3_36),
% 4.08/0.90    inference(avatar_split_clause,[],[f1494,f824,f47,f3510])).
% 4.08/0.90  fof(f3510,plain,(
% 4.08/0.90    spl3_77 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 4.08/0.90  fof(f47,plain,(
% 4.08/0.90    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.08/0.90  fof(f824,plain,(
% 4.08/0.90    spl3_36 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 4.08/0.90  fof(f1494,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1) | (~spl3_3 | ~spl3_36)),
% 4.08/0.90    inference(forward_demodulation,[],[f1455,f826])).
% 4.08/0.90  fof(f826,plain,(
% 4.08/0.90    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | ~spl3_36),
% 4.08/0.90    inference(avatar_component_clause,[],[f824])).
% 4.08/0.90  fof(f1455,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK1)) | ~spl3_3),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f49,f365])).
% 4.08/0.90  fof(f365,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X0,k4_subset_1(X0,X1,X2)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.90    inference(forward_demodulation,[],[f357,f29])).
% 4.08/0.90  fof(f29,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f1])).
% 4.08/0.90  fof(f1,axiom,(
% 4.08/0.90    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.08/0.90  fof(f357,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (k2_xboole_0(k4_subset_1(X0,X1,X2),X0) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.90    inference(resolution,[],[f58,f34])).
% 4.08/0.90  fof(f58,plain,(
% 4.08/0.90    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = X3) )),
% 4.08/0.90    inference(resolution,[],[f30,f32])).
% 4.08/0.90  fof(f32,plain,(
% 4.08/0.90    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f7])).
% 4.08/0.90  fof(f30,plain,(
% 4.08/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.08/0.90    inference(cnf_transformation,[],[f16])).
% 4.08/0.90  fof(f16,plain,(
% 4.08/0.90    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.08/0.90    inference(ennf_transformation,[],[f3])).
% 4.08/0.90  fof(f3,axiom,(
% 4.08/0.90    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.08/0.90  fof(f49,plain,(
% 4.08/0.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 4.08/0.90    inference(avatar_component_clause,[],[f47])).
% 4.08/0.90  fof(f3492,plain,(
% 4.08/0.90    spl3_76 | ~spl3_1 | ~spl3_10 | ~spl3_32),
% 4.08/0.90    inference(avatar_split_clause,[],[f814,f664,f149,f37,f3489])).
% 4.08/0.90  fof(f3489,plain,(
% 4.08/0.90    spl3_76 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 4.08/0.90  fof(f37,plain,(
% 4.08/0.90    spl3_1 <=> l1_pre_topc(sK0)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.08/0.90  fof(f149,plain,(
% 4.08/0.90    spl3_10 <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 4.08/0.90  fof(f664,plain,(
% 4.08/0.90    spl3_32 <=> r1_tarski(sK1,sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 4.08/0.90  fof(f814,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_10 | ~spl3_32)),
% 4.08/0.90    inference(backward_demodulation,[],[f701,f792])).
% 4.08/0.90  fof(f792,plain,(
% 4.08/0.90    sK1 = k2_xboole_0(sK1,sK1) | ~spl3_32),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f666,f30])).
% 4.08/0.90  fof(f666,plain,(
% 4.08/0.90    r1_tarski(sK1,sK1) | ~spl3_32),
% 4.08/0.90    inference(avatar_component_clause,[],[f664])).
% 4.08/0.90  fof(f701,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,k2_xboole_0(sK1,sK1)),k1_tops_1(sK0,k2_xboole_0(sK1,sK1))) | (~spl3_1 | ~spl3_10)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f151,f151,f343,f27])).
% 4.08/0.90  fof(f27,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f15])).
% 4.08/0.90  fof(f15,plain,(
% 4.08/0.90    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.08/0.90    inference(flattening,[],[f14])).
% 4.08/0.90  fof(f14,plain,(
% 4.08/0.90    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.08/0.90    inference(ennf_transformation,[],[f9])).
% 4.08/0.90  fof(f9,axiom,(
% 4.08/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 4.08/0.90  fof(f343,plain,(
% 4.08/0.90    ( ! [X8,X9] : (r1_tarski(k2_xboole_0(X8,X9),k2_xboole_0(X8,X9))) )),
% 4.08/0.90    inference(superposition,[],[f51,f56])).
% 4.08/0.90  fof(f56,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f28,f30])).
% 4.08/0.90  fof(f28,plain,(
% 4.08/0.90    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f4])).
% 4.08/0.90  fof(f4,axiom,(
% 4.08/0.90    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.08/0.90  fof(f51,plain,(
% 4.08/0.90    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 4.08/0.90    inference(superposition,[],[f28,f29])).
% 4.08/0.90  fof(f151,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 4.08/0.90    inference(avatar_component_clause,[],[f149])).
% 4.08/0.90  fof(f39,plain,(
% 4.08/0.90    l1_pre_topc(sK0) | ~spl3_1),
% 4.08/0.90    inference(avatar_component_clause,[],[f37])).
% 4.08/0.90  fof(f3486,plain,(
% 4.08/0.90    spl3_75 | ~spl3_3 | ~spl3_23),
% 4.08/0.90    inference(avatar_split_clause,[],[f2204,f451,f47,f3483])).
% 4.08/0.90  fof(f3483,plain,(
% 4.08/0.90    spl3_75 <=> k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 4.08/0.90  fof(f451,plain,(
% 4.08/0.90    spl3_23 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 4.08/0.90  fof(f2204,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) | (~spl3_3 | ~spl3_23)),
% 4.08/0.90    inference(forward_demodulation,[],[f2113,f29])).
% 4.08/0.90  fof(f2113,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK1) = k2_xboole_0(k1_tops_1(sK0,sK2),sK1) | (~spl3_3 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f452,f35])).
% 4.08/0.90  fof(f452,plain,(
% 4.08/0.90    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_23),
% 4.08/0.90    inference(avatar_component_clause,[],[f451])).
% 4.08/0.90  fof(f3481,plain,(
% 4.08/0.90    spl3_74 | ~spl3_23 | ~spl3_34),
% 4.08/0.90    inference(avatar_split_clause,[],[f2191,f767,f451,f3478])).
% 4.08/0.90  fof(f3478,plain,(
% 4.08/0.90    spl3_74 <=> k1_tops_1(sK0,sK2) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 4.08/0.90  fof(f767,plain,(
% 4.08/0.90    spl3_34 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 4.08/0.90  fof(f2191,plain,(
% 4.08/0.90    k1_tops_1(sK0,sK2) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | (~spl3_23 | ~spl3_34)),
% 4.08/0.90    inference(forward_demodulation,[],[f2118,f777])).
% 4.08/0.90  fof(f777,plain,(
% 4.08/0.90    k1_tops_1(sK0,sK2) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | ~spl3_34),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f769,f30])).
% 4.08/0.90  fof(f769,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | ~spl3_34),
% 4.08/0.90    inference(avatar_component_clause,[],[f767])).
% 4.08/0.90  fof(f2118,plain,(
% 4.08/0.90    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | ~spl3_23),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f452,f452,f35])).
% 4.08/0.90  fof(f3476,plain,(
% 4.08/0.90    spl3_73 | ~spl3_3 | ~spl3_23),
% 4.08/0.90    inference(avatar_split_clause,[],[f2119,f451,f47,f3473])).
% 4.08/0.90  fof(f3473,plain,(
% 4.08/0.90    spl3_73 <=> k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 4.08/0.90  fof(f2119,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) | (~spl3_3 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f452,f35])).
% 4.08/0.90  fof(f3471,plain,(
% 4.08/0.90    spl3_72 | ~spl3_30),
% 4.08/0.90    inference(avatar_split_clause,[],[f592,f550,f3468])).
% 4.08/0.90  fof(f3468,plain,(
% 4.08/0.90    spl3_72 <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 4.08/0.90  fof(f550,plain,(
% 4.08/0.90    spl3_30 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 4.08/0.90  fof(f592,plain,(
% 4.08/0.90    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_30),
% 4.08/0.90    inference(superposition,[],[f552,f29])).
% 4.08/0.90  fof(f552,plain,(
% 4.08/0.90    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl3_30),
% 4.08/0.90    inference(avatar_component_clause,[],[f550])).
% 4.08/0.90  fof(f3466,plain,(
% 4.08/0.90    spl3_71 | ~spl3_2 | ~spl3_22),
% 4.08/0.90    inference(avatar_split_clause,[],[f2048,f447,f42,f3463])).
% 4.08/0.90  fof(f3463,plain,(
% 4.08/0.90    spl3_71 <=> k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 4.08/0.90  fof(f42,plain,(
% 4.08/0.90    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.08/0.90  fof(f447,plain,(
% 4.08/0.90    spl3_22 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 4.08/0.90  fof(f2048,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_22)),
% 4.08/0.90    inference(forward_demodulation,[],[f1973,f29])).
% 4.08/0.90  fof(f1973,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK2) = k2_xboole_0(k1_tops_1(sK0,sK1),sK2) | (~spl3_2 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f448,f35])).
% 4.08/0.90  fof(f448,plain,(
% 4.08/0.90    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_22),
% 4.08/0.90    inference(avatar_component_clause,[],[f447])).
% 4.08/0.90  fof(f44,plain,(
% 4.08/0.90    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.08/0.90    inference(avatar_component_clause,[],[f42])).
% 4.08/0.90  fof(f3461,plain,(
% 4.08/0.90    spl3_70 | ~spl3_1 | ~spl3_3 | ~spl3_22 | ~spl3_32),
% 4.08/0.90    inference(avatar_split_clause,[],[f2041,f664,f447,f47,f37,f3458])).
% 4.08/0.90  fof(f3458,plain,(
% 4.08/0.90    spl3_70 <=> k1_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 4.08/0.90  fof(f2041,plain,(
% 4.08/0.90    k1_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_3 | ~spl3_22 | ~spl3_32)),
% 4.08/0.90    inference(forward_demodulation,[],[f1976,f1547])).
% 4.08/0.90  fof(f1547,plain,(
% 4.08/0.90    k1_tops_1(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_3 | ~spl3_32)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f666,f49,f49,f445])).
% 4.08/0.90  fof(f445,plain,(
% 4.08/0.90    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X3) = k2_xboole_0(k1_tops_1(sK0,X4),k1_tops_1(sK0,X3))) ) | ~spl3_1),
% 4.08/0.90    inference(resolution,[],[f115,f30])).
% 4.08/0.90  fof(f115,plain,(
% 4.08/0.90    ( ! [X0,X1] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 4.08/0.90    inference(resolution,[],[f27,f39])).
% 4.08/0.90  fof(f1976,plain,(
% 4.08/0.90    k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_22),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f448,f448,f35])).
% 4.08/0.90  fof(f3456,plain,(
% 4.08/0.90    spl3_69 | ~spl3_2 | ~spl3_22),
% 4.08/0.90    inference(avatar_split_clause,[],[f1978,f447,f42,f3453])).
% 4.08/0.90  fof(f3453,plain,(
% 4.08/0.90    spl3_69 <=> k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 4.08/0.90  fof(f1978,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK2,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f448,f35])).
% 4.08/0.90  fof(f3209,plain,(
% 4.08/0.90    spl3_68 | ~spl3_29),
% 4.08/0.90    inference(avatar_split_clause,[],[f580,f538,f3206])).
% 4.08/0.90  fof(f3206,plain,(
% 4.08/0.90    spl3_68 <=> sK2 = k2_xboole_0(sK2,k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 4.08/0.90  fof(f538,plain,(
% 4.08/0.90    spl3_29 <=> sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 4.08/0.90  fof(f580,plain,(
% 4.08/0.90    sK2 = k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) | ~spl3_29),
% 4.08/0.90    inference(superposition,[],[f540,f29])).
% 4.08/0.90  fof(f540,plain,(
% 4.08/0.90    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) | ~spl3_29),
% 4.08/0.90    inference(avatar_component_clause,[],[f538])).
% 4.08/0.90  fof(f2751,plain,(
% 4.08/0.90    spl3_67 | ~spl3_22 | ~spl3_23),
% 4.08/0.90    inference(avatar_split_clause,[],[f2131,f451,f447,f2748])).
% 4.08/0.90  fof(f2748,plain,(
% 4.08/0.90    spl3_67 <=> m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 4.08/0.90  fof(f2131,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_22 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f448,f452,f93])).
% 4.08/0.90  fof(f2746,plain,(
% 4.08/0.90    spl3_66 | ~spl3_11 | ~spl3_23),
% 4.08/0.90    inference(avatar_split_clause,[],[f2129,f451,f154,f2743])).
% 4.08/0.90  fof(f2743,plain,(
% 4.08/0.90    spl3_66 <=> m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 4.08/0.90  fof(f154,plain,(
% 4.08/0.90    spl3_11 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 4.08/0.90  fof(f2129,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_11 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f156,f452,f93])).
% 4.08/0.90  fof(f156,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 4.08/0.90    inference(avatar_component_clause,[],[f154])).
% 4.08/0.90  fof(f2732,plain,(
% 4.08/0.90    spl3_65 | ~spl3_11 | ~spl3_22),
% 4.08/0.90    inference(avatar_split_clause,[],[f1986,f447,f154,f2729])).
% 4.08/0.90  fof(f2729,plain,(
% 4.08/0.90    spl3_65 <=> m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 4.08/0.90  fof(f1986,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_11 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f156,f448,f93])).
% 4.08/0.90  fof(f2308,plain,(
% 4.08/0.90    spl3_64 | ~spl3_2 | ~spl3_23 | ~spl3_29),
% 4.08/0.90    inference(avatar_split_clause,[],[f2202,f538,f451,f42,f2305])).
% 4.08/0.90  fof(f2305,plain,(
% 4.08/0.90    spl3_64 <=> sK2 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 4.08/0.90  fof(f2202,plain,(
% 4.08/0.90    sK2 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_23 | ~spl3_29)),
% 4.08/0.90    inference(forward_demodulation,[],[f2201,f580])).
% 4.08/0.90  fof(f2201,plain,(
% 4.08/0.90    k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_23)),
% 4.08/0.90    inference(forward_demodulation,[],[f2114,f29])).
% 4.08/0.90  fof(f2114,plain,(
% 4.08/0.90    k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f452,f35])).
% 4.08/0.90  fof(f2303,plain,(
% 4.08/0.90    spl3_63 | ~spl3_2 | ~spl3_23 | ~spl3_29),
% 4.08/0.90    inference(avatar_split_clause,[],[f2188,f538,f451,f42,f2300])).
% 4.08/0.90  fof(f2300,plain,(
% 4.08/0.90    spl3_63 <=> sK2 = k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 4.08/0.90  fof(f2188,plain,(
% 4.08/0.90    sK2 = k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK2)) | (~spl3_2 | ~spl3_23 | ~spl3_29)),
% 4.08/0.90    inference(forward_demodulation,[],[f2120,f580])).
% 4.08/0.90  fof(f2120,plain,(
% 4.08/0.90    k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,k1_tops_1(sK0,sK2)) | (~spl3_2 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f452,f35])).
% 4.08/0.90  fof(f2289,plain,(
% 4.08/0.90    spl3_26 | ~spl3_9 | ~spl3_28),
% 4.08/0.90    inference(avatar_split_clause,[],[f1932,f518,f127,f501])).
% 4.08/0.90  fof(f501,plain,(
% 4.08/0.90    spl3_26 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 4.08/0.90  fof(f127,plain,(
% 4.08/0.90    spl3_9 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 4.08/0.90  fof(f518,plain,(
% 4.08/0.90    spl3_28 <=> u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 4.08/0.90  fof(f1932,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl3_9 | ~spl3_28)),
% 4.08/0.90    inference(superposition,[],[f547,f520])).
% 4.08/0.90  fof(f520,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) | ~spl3_28),
% 4.08/0.90    inference(avatar_component_clause,[],[f518])).
% 4.08/0.90  fof(f547,plain,(
% 4.08/0.90    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X0))) ) | ~spl3_9),
% 4.08/0.90    inference(superposition,[],[f136,f29])).
% 4.08/0.90  fof(f136,plain,(
% 4.08/0.90    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))) ) | ~spl3_9),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f129,f33])).
% 4.08/0.90  fof(f33,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f17])).
% 4.08/0.90  fof(f17,plain,(
% 4.08/0.90    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.08/0.90    inference(ennf_transformation,[],[f2])).
% 4.08/0.90  fof(f2,axiom,(
% 4.08/0.90    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 4.08/0.90  fof(f129,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_9),
% 4.08/0.90    inference(avatar_component_clause,[],[f127])).
% 4.08/0.90  fof(f2288,plain,(
% 4.08/0.90    spl3_62 | ~spl3_3 | ~spl3_23),
% 4.08/0.90    inference(avatar_split_clause,[],[f2133,f451,f47,f2285])).
% 4.08/0.90  fof(f2285,plain,(
% 4.08/0.90    spl3_62 <=> m1_subset_1(k2_xboole_0(sK1,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 4.08/0.90  fof(f2133,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK1,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f452,f93])).
% 4.08/0.90  fof(f2283,plain,(
% 4.08/0.90    spl3_61 | ~spl3_1 | ~spl3_23),
% 4.08/0.90    inference(avatar_split_clause,[],[f2095,f451,f37,f2280])).
% 4.08/0.90  fof(f2280,plain,(
% 4.08/0.90    spl3_61 <=> r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 4.08/0.90  fof(f2095,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) | (~spl3_1 | ~spl3_23)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f452,f26])).
% 4.08/0.90  fof(f26,plain,(
% 4.08/0.90    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f13])).
% 4.08/0.90  fof(f13,plain,(
% 4.08/0.90    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.08/0.90    inference(ennf_transformation,[],[f8])).
% 4.08/0.90  fof(f8,axiom,(
% 4.08/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 4.08/0.90  fof(f2278,plain,(
% 4.08/0.90    spl3_60 | ~spl3_3 | ~spl3_22 | ~spl3_30),
% 4.08/0.90    inference(avatar_split_clause,[],[f2051,f550,f447,f47,f2275])).
% 4.08/0.90  fof(f2275,plain,(
% 4.08/0.90    spl3_60 <=> sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 4.08/0.90  fof(f2051,plain,(
% 4.08/0.90    sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_22 | ~spl3_30)),
% 4.08/0.90    inference(forward_demodulation,[],[f2050,f592])).
% 4.08/0.90  fof(f2050,plain,(
% 4.08/0.90    k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_22)),
% 4.08/0.90    inference(forward_demodulation,[],[f1972,f29])).
% 4.08/0.90  fof(f1972,plain,(
% 4.08/0.90    k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f448,f35])).
% 4.08/0.90  fof(f2273,plain,(
% 4.08/0.90    spl3_59 | ~spl3_3 | ~spl3_22 | ~spl3_30),
% 4.08/0.90    inference(avatar_split_clause,[],[f2039,f550,f447,f47,f2270])).
% 4.08/0.90  fof(f2270,plain,(
% 4.08/0.90    spl3_59 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 4.08/0.90  fof(f2039,plain,(
% 4.08/0.90    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_22 | ~spl3_30)),
% 4.08/0.90    inference(forward_demodulation,[],[f1977,f592])).
% 4.08/0.90  fof(f1977,plain,(
% 4.08/0.90    k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f448,f35])).
% 4.08/0.90  fof(f2268,plain,(
% 4.08/0.90    spl3_58 | ~spl3_8 | ~spl3_27),
% 4.08/0.90    inference(avatar_split_clause,[],[f1920,f513,f122,f2265])).
% 4.08/0.90  fof(f2265,plain,(
% 4.08/0.90    spl3_58 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 4.08/0.90  fof(f122,plain,(
% 4.08/0.90    spl3_8 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 4.08/0.90  fof(f513,plain,(
% 4.08/0.90    spl3_27 <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 4.08/0.90  fof(f1920,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | (~spl3_8 | ~spl3_27)),
% 4.08/0.90    inference(superposition,[],[f535,f515])).
% 4.08/0.90  fof(f515,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl3_27),
% 4.08/0.90    inference(avatar_component_clause,[],[f513])).
% 4.08/0.90  fof(f535,plain,(
% 4.08/0.90    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(sK2,X0))) ) | ~spl3_8),
% 4.08/0.90    inference(superposition,[],[f131,f29])).
% 4.08/0.90  fof(f131,plain,(
% 4.08/0.90    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2))) ) | ~spl3_8),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f124,f33])).
% 4.08/0.90  fof(f124,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_8),
% 4.08/0.90    inference(avatar_component_clause,[],[f122])).
% 4.08/0.90  fof(f2263,plain,(
% 4.08/0.90    spl3_57 | ~spl3_2 | ~spl3_22),
% 4.08/0.90    inference(avatar_split_clause,[],[f1990,f447,f42,f2260])).
% 4.08/0.90  fof(f2260,plain,(
% 4.08/0.90    spl3_57 <=> m1_subset_1(k2_xboole_0(sK2,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 4.08/0.90  fof(f1990,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK2,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f448,f93])).
% 4.08/0.90  fof(f2258,plain,(
% 4.08/0.90    spl3_56 | ~spl3_1 | ~spl3_22),
% 4.08/0.90    inference(avatar_split_clause,[],[f1957,f447,f37,f2255])).
% 4.08/0.90  fof(f2255,plain,(
% 4.08/0.90    spl3_56 <=> r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 4.08/0.90  fof(f1957,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_22)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f448,f26])).
% 4.08/0.90  fof(f2233,plain,(
% 4.08/0.90    spl3_55 | ~spl3_32 | ~spl3_43),
% 4.08/0.90    inference(avatar_split_clause,[],[f1129,f870,f664,f2230])).
% 4.08/0.90  fof(f2230,plain,(
% 4.08/0.90    spl3_55 <=> sK1 = k4_subset_1(sK1,sK1,sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 4.08/0.90  fof(f870,plain,(
% 4.08/0.90    spl3_43 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 4.08/0.90  fof(f1129,plain,(
% 4.08/0.90    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl3_32 | ~spl3_43)),
% 4.08/0.90    inference(forward_demodulation,[],[f1116,f792])).
% 4.08/0.90  fof(f1116,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | ~spl3_43),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f872,f872,f35])).
% 4.08/0.90  fof(f872,plain,(
% 4.08/0.90    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_43),
% 4.08/0.90    inference(avatar_component_clause,[],[f870])).
% 4.08/0.90  fof(f2075,plain,(
% 4.08/0.90    ~spl3_8 | spl3_23 | ~spl3_27),
% 4.08/0.90    inference(avatar_contradiction_clause,[],[f2074])).
% 4.08/0.90  fof(f2074,plain,(
% 4.08/0.90    $false | (~spl3_8 | spl3_23 | ~spl3_27)),
% 4.08/0.90    inference(subsumption_resolution,[],[f2071,f1920])).
% 4.08/0.90  fof(f2071,plain,(
% 4.08/0.90    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_23),
% 4.08/0.90    inference(resolution,[],[f453,f31])).
% 4.08/0.90  fof(f453,plain,(
% 4.08/0.90    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_23),
% 4.08/0.90    inference(avatar_component_clause,[],[f451])).
% 4.08/0.90  fof(f2073,plain,(
% 4.08/0.90    ~spl3_8 | spl3_23 | ~spl3_27),
% 4.08/0.90    inference(avatar_contradiction_clause,[],[f2072])).
% 4.08/0.90  fof(f2072,plain,(
% 4.08/0.90    $false | (~spl3_8 | spl3_23 | ~spl3_27)),
% 4.08/0.90    inference(subsumption_resolution,[],[f2070,f1920])).
% 4.08/0.90  fof(f2070,plain,(
% 4.08/0.90    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_23),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f453,f31])).
% 4.08/0.90  fof(f1945,plain,(
% 4.08/0.90    spl3_54 | ~spl3_31 | ~spl3_39),
% 4.08/0.90    inference(avatar_split_clause,[],[f941,f845,f605,f1942])).
% 4.08/0.90  fof(f1942,plain,(
% 4.08/0.90    spl3_54 <=> sK2 = k4_subset_1(sK2,sK2,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 4.08/0.90  fof(f605,plain,(
% 4.08/0.90    spl3_31 <=> r1_tarski(sK2,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 4.08/0.90  fof(f845,plain,(
% 4.08/0.90    spl3_39 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 4.08/0.90  fof(f941,plain,(
% 4.08/0.90    sK2 = k4_subset_1(sK2,sK2,sK2) | (~spl3_31 | ~spl3_39)),
% 4.08/0.90    inference(forward_demodulation,[],[f928,f730])).
% 4.08/0.90  fof(f730,plain,(
% 4.08/0.90    sK2 = k2_xboole_0(sK2,sK2) | ~spl3_31),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f607,f30])).
% 4.08/0.90  fof(f607,plain,(
% 4.08/0.90    r1_tarski(sK2,sK2) | ~spl3_31),
% 4.08/0.90    inference(avatar_component_clause,[],[f605])).
% 4.08/0.90  fof(f928,plain,(
% 4.08/0.90    k2_xboole_0(sK2,sK2) = k4_subset_1(sK2,sK2,sK2) | ~spl3_39),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f847,f847,f35])).
% 4.08/0.90  fof(f847,plain,(
% 4.08/0.90    m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~spl3_39),
% 4.08/0.90    inference(avatar_component_clause,[],[f845])).
% 4.08/0.90  fof(f1940,plain,(
% 4.08/0.90    ~spl3_9 | spl3_26 | ~spl3_28),
% 4.08/0.90    inference(avatar_contradiction_clause,[],[f1939])).
% 4.08/0.90  fof(f1939,plain,(
% 4.08/0.90    $false | (~spl3_9 | spl3_26 | ~spl3_28)),
% 4.08/0.90    inference(subsumption_resolution,[],[f1932,f503])).
% 4.08/0.90  fof(f503,plain,(
% 4.08/0.90    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_26),
% 4.08/0.90    inference(avatar_component_clause,[],[f501])).
% 4.08/0.90  fof(f1569,plain,(
% 4.08/0.90    spl3_53 | ~spl3_28),
% 4.08/0.90    inference(avatar_split_clause,[],[f630,f518,f1566])).
% 4.08/0.90  fof(f1566,plain,(
% 4.08/0.90    spl3_53 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 4.08/0.90  fof(f630,plain,(
% 4.08/0.90    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_28),
% 4.08/0.90    inference(superposition,[],[f143,f520])).
% 4.08/0.90  fof(f143,plain,(
% 4.08/0.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_xboole_0(X1,X0)))) )),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f51,f31])).
% 4.08/0.90  fof(f1564,plain,(
% 4.08/0.90    ~spl3_22 | ~spl3_23 | ~spl3_52 | spl3_20),
% 4.08/0.90    inference(avatar_split_clause,[],[f384,f378,f1561,f451,f447])).
% 4.08/0.90  fof(f378,plain,(
% 4.08/0.90    spl3_20 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 4.08/0.90  fof(f384,plain,(
% 4.08/0.90    ~m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 4.08/0.90    inference(superposition,[],[f380,f35])).
% 4.08/0.90  fof(f380,plain,(
% 4.08/0.90    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_20),
% 4.08/0.90    inference(avatar_component_clause,[],[f378])).
% 4.08/0.90  fof(f1326,plain,(
% 4.08/0.90    spl3_51 | ~spl3_32),
% 4.08/0.90    inference(avatar_split_clause,[],[f792,f664,f1323])).
% 4.08/0.90  fof(f1323,plain,(
% 4.08/0.90    spl3_51 <=> sK1 = k2_xboole_0(sK1,sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 4.08/0.90  fof(f1249,plain,(
% 4.08/0.90    spl3_50 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f719,f154,f1246])).
% 4.08/0.90  fof(f1246,plain,(
% 4.08/0.90    spl3_50 <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 4.08/0.90  fof(f719,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | ~spl3_11),
% 4.08/0.90    inference(backward_demodulation,[],[f205,f705])).
% 4.08/0.90  fof(f705,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f343,f30])).
% 4.08/0.90  fof(f205,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | ~spl3_11),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f156,f156,f35])).
% 4.08/0.90  fof(f1244,plain,(
% 4.08/0.90    spl3_49 | ~spl3_31),
% 4.08/0.90    inference(avatar_split_clause,[],[f730,f605,f1241])).
% 4.08/0.90  fof(f1241,plain,(
% 4.08/0.90    spl3_49 <=> sK2 = k2_xboole_0(sK2,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 4.08/0.90  fof(f1185,plain,(
% 4.08/0.90    spl3_48 | ~spl3_2 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f227,f154,f42,f1182])).
% 4.08/0.90  fof(f1182,plain,(
% 4.08/0.90    spl3_48 <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 4.08/0.90  fof(f227,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) | (~spl3_2 | ~spl3_11)),
% 4.08/0.90    inference(forward_demodulation,[],[f226,f142])).
% 4.08/0.90  fof(f142,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f51,f30])).
% 4.08/0.90  fof(f226,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_11)),
% 4.08/0.90    inference(forward_demodulation,[],[f198,f29])).
% 4.08/0.90  fof(f198,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2) | (~spl3_2 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f156,f35])).
% 4.08/0.90  fof(f1180,plain,(
% 4.08/0.90    spl3_47 | ~spl3_27),
% 4.08/0.90    inference(avatar_split_clause,[],[f565,f513,f1177])).
% 4.08/0.90  fof(f1177,plain,(
% 4.08/0.90    spl3_47 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 4.08/0.90  fof(f565,plain,(
% 4.08/0.90    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl3_27),
% 4.08/0.90    inference(superposition,[],[f51,f515])).
% 4.08/0.90  fof(f1175,plain,(
% 4.08/0.90    spl3_46 | ~spl3_3 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f224,f154,f47,f1172])).
% 4.08/0.90  fof(f1172,plain,(
% 4.08/0.90    spl3_46 <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 4.08/0.90  fof(f224,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) | (~spl3_3 | ~spl3_11)),
% 4.08/0.90    inference(forward_demodulation,[],[f223,f56])).
% 4.08/0.90  fof(f223,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_11)),
% 4.08/0.90    inference(forward_demodulation,[],[f199,f29])).
% 4.08/0.90  fof(f199,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK1) | (~spl3_3 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f156,f35])).
% 4.08/0.90  fof(f1170,plain,(
% 4.08/0.90    spl3_45 | ~spl3_2 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f219,f154,f42,f1167])).
% 4.08/0.90  fof(f1167,plain,(
% 4.08/0.90    spl3_45 <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 4.08/0.90  fof(f219,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_11)),
% 4.08/0.90    inference(forward_demodulation,[],[f202,f142])).
% 4.08/0.90  fof(f202,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f156,f35])).
% 4.08/0.90  fof(f1165,plain,(
% 4.08/0.90    spl3_44 | ~spl3_3 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f217,f154,f47,f1162])).
% 4.08/0.90  fof(f1162,plain,(
% 4.08/0.90    spl3_44 <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 4.08/0.90  fof(f217,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_11)),
% 4.08/0.90    inference(forward_demodulation,[],[f203,f56])).
% 4.08/0.90  fof(f203,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f156,f35])).
% 4.08/0.90  fof(f873,plain,(
% 4.08/0.90    spl3_43 | ~spl3_30),
% 4.08/0.90    inference(avatar_split_clause,[],[f629,f550,f870])).
% 4.08/0.90  fof(f629,plain,(
% 4.08/0.90    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_30),
% 4.08/0.90    inference(superposition,[],[f143,f552])).
% 4.08/0.90  fof(f863,plain,(
% 4.08/0.90    spl3_42 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_31),
% 4.08/0.90    inference(avatar_split_clause,[],[f764,f605,f166,f154,f42,f860])).
% 4.08/0.90  fof(f860,plain,(
% 4.08/0.90    spl3_42 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 4.08/0.90  fof(f166,plain,(
% 4.08/0.90    spl3_12 <=> m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 4.08/0.90  fof(f764,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_31)),
% 4.08/0.90    inference(forward_demodulation,[],[f744,f219])).
% 4.08/0.90  fof(f744,plain,(
% 4.08/0.90    k2_xboole_0(k2_xboole_0(sK1,sK2),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_12 | ~spl3_31)),
% 4.08/0.90    inference(backward_demodulation,[],[f259,f730])).
% 4.08/0.90  fof(f259,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK2)) | (~spl3_11 | ~spl3_12)),
% 4.08/0.90    inference(forward_demodulation,[],[f235,f29])).
% 4.08/0.90  fof(f235,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_12)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f156,f168,f35])).
% 4.08/0.90  fof(f168,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_12),
% 4.08/0.90    inference(avatar_component_clause,[],[f166])).
% 4.08/0.90  fof(f858,plain,(
% 4.08/0.90    spl3_41 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f354,f154,f855])).
% 4.08/0.90  fof(f855,plain,(
% 4.08/0.90    spl3_41 <=> u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 4.08/0.90  fof(f354,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~spl3_11),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f156,f58])).
% 4.08/0.90  fof(f853,plain,(
% 4.08/0.90    spl3_40 | ~spl3_1 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f197,f154,f37,f850])).
% 4.08/0.90  fof(f850,plain,(
% 4.08/0.90    spl3_40 <=> r1_tarski(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 4.08/0.90  fof(f197,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f156,f26])).
% 4.08/0.90  fof(f848,plain,(
% 4.08/0.90    spl3_39 | ~spl3_29),
% 4.08/0.90    inference(avatar_split_clause,[],[f628,f538,f845])).
% 4.08/0.90  fof(f628,plain,(
% 4.08/0.90    m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~spl3_29),
% 4.08/0.90    inference(superposition,[],[f143,f540])).
% 4.08/0.90  fof(f843,plain,(
% 4.08/0.90    spl3_38 | ~spl3_1 | ~spl3_2 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f196,f154,f42,f37,f840])).
% 4.08/0.90  fof(f196,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f44,f51,f156,f27])).
% 4.08/0.90  fof(f838,plain,(
% 4.08/0.90    spl3_37 | ~spl3_1 | ~spl3_3 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f195,f154,f47,f37,f835])).
% 4.08/0.90  fof(f195,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_3 | ~spl3_11)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f49,f28,f156,f27])).
% 4.08/0.90  fof(f827,plain,(
% 4.08/0.90    spl3_36 | ~spl3_3 | ~spl3_10 | ~spl3_32),
% 4.08/0.90    inference(avatar_split_clause,[],[f799,f664,f149,f47,f824])).
% 4.08/0.90  fof(f799,plain,(
% 4.08/0.90    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | (~spl3_3 | ~spl3_10 | ~spl3_32)),
% 4.08/0.90    inference(backward_demodulation,[],[f187,f792])).
% 4.08/0.90  fof(f187,plain,(
% 4.08/0.90    k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)) | (~spl3_3 | ~spl3_10)),
% 4.08/0.90    inference(forward_demodulation,[],[f177,f56])).
% 4.08/0.90  fof(f177,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)) | (~spl3_3 | ~spl3_10)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f151,f35])).
% 4.08/0.90  fof(f775,plain,(
% 4.08/0.90    spl3_35 | ~spl3_2 | ~spl3_12 | ~spl3_31),
% 4.08/0.90    inference(avatar_split_clause,[],[f743,f605,f166,f42,f772])).
% 4.08/0.90  fof(f772,plain,(
% 4.08/0.90    spl3_35 <=> sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 4.08/0.90  fof(f743,plain,(
% 4.08/0.90    sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) | (~spl3_2 | ~spl3_12 | ~spl3_31)),
% 4.08/0.90    inference(backward_demodulation,[],[f257,f730])).
% 4.08/0.90  fof(f257,plain,(
% 4.08/0.90    k2_xboole_0(sK2,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK2)) | (~spl3_2 | ~spl3_12)),
% 4.08/0.90    inference(forward_demodulation,[],[f237,f56])).
% 4.08/0.90  fof(f237,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK2,sK2)) | (~spl3_2 | ~spl3_12)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f168,f35])).
% 4.08/0.90  fof(f770,plain,(
% 4.08/0.90    spl3_34 | ~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_31),
% 4.08/0.90    inference(avatar_split_clause,[],[f735,f605,f166,f42,f37,f767])).
% 4.08/0.90  fof(f735,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_31)),
% 4.08/0.90    inference(backward_demodulation,[],[f230,f730])).
% 4.08/0.90  fof(f230,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_12)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f44,f51,f168,f27])).
% 4.08/0.90  fof(f726,plain,(
% 4.08/0.90    spl3_33 | ~spl3_1 | ~spl3_3 | ~spl3_10),
% 4.08/0.90    inference(avatar_split_clause,[],[f171,f149,f47,f37,f723])).
% 4.08/0.90  fof(f723,plain,(
% 4.08/0.90    spl3_33 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK1)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 4.08/0.90  fof(f171,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK1))) | (~spl3_1 | ~spl3_3 | ~spl3_10)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f49,f51,f151,f27])).
% 4.08/0.90  fof(f667,plain,(
% 4.08/0.90    spl3_32 | ~spl3_30),
% 4.08/0.90    inference(avatar_split_clause,[],[f598,f550,f664])).
% 4.08/0.90  fof(f598,plain,(
% 4.08/0.90    r1_tarski(sK1,sK1) | ~spl3_30),
% 4.08/0.90    inference(superposition,[],[f51,f552])).
% 4.08/0.90  fof(f608,plain,(
% 4.08/0.90    spl3_31 | ~spl3_29),
% 4.08/0.90    inference(avatar_split_clause,[],[f586,f538,f605])).
% 4.08/0.90  fof(f586,plain,(
% 4.08/0.90    r1_tarski(sK2,sK2) | ~spl3_29),
% 4.08/0.90    inference(superposition,[],[f51,f540])).
% 4.08/0.90  fof(f553,plain,(
% 4.08/0.90    spl3_30 | ~spl3_9),
% 4.08/0.90    inference(avatar_split_clause,[],[f137,f127,f550])).
% 4.08/0.90  fof(f137,plain,(
% 4.08/0.90    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl3_9),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f129,f30])).
% 4.08/0.90  fof(f541,plain,(
% 4.08/0.90    spl3_29 | ~spl3_8),
% 4.08/0.90    inference(avatar_split_clause,[],[f132,f122,f538])).
% 4.08/0.90  fof(f132,plain,(
% 4.08/0.90    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) | ~spl3_8),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f124,f30])).
% 4.08/0.90  fof(f521,plain,(
% 4.08/0.90    spl3_28 | ~spl3_6),
% 4.08/0.90    inference(avatar_split_clause,[],[f117,f78,f518])).
% 4.08/0.90  fof(f78,plain,(
% 4.08/0.90    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 4.08/0.90  fof(f117,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f80,f30])).
% 4.08/0.90  fof(f80,plain,(
% 4.08/0.90    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 4.08/0.90    inference(avatar_component_clause,[],[f78])).
% 4.08/0.90  fof(f516,plain,(
% 4.08/0.90    spl3_27 | ~spl3_4),
% 4.08/0.90    inference(avatar_split_clause,[],[f111,f60,f513])).
% 4.08/0.90  fof(f60,plain,(
% 4.08/0.90    spl3_4 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.08/0.90  fof(f111,plain,(
% 4.08/0.90    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl3_4),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f62,f30])).
% 4.08/0.90  fof(f62,plain,(
% 4.08/0.90    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_4),
% 4.08/0.90    inference(avatar_component_clause,[],[f60])).
% 4.08/0.90  fof(f504,plain,(
% 4.08/0.90    ~spl3_26 | spl3_22),
% 4.08/0.90    inference(avatar_split_clause,[],[f459,f447,f501])).
% 4.08/0.90  fof(f459,plain,(
% 4.08/0.90    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_22),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f449,f31])).
% 4.08/0.90  fof(f449,plain,(
% 4.08/0.90    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_22),
% 4.08/0.90    inference(avatar_component_clause,[],[f447])).
% 4.08/0.90  fof(f465,plain,(
% 4.08/0.90    spl3_25 | ~spl3_12),
% 4.08/0.90    inference(avatar_split_clause,[],[f252,f166,f462])).
% 4.08/0.90  fof(f462,plain,(
% 4.08/0.90    spl3_25 <=> r1_tarski(k2_xboole_0(sK2,sK2),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 4.08/0.90  fof(f252,plain,(
% 4.08/0.90    r1_tarski(k2_xboole_0(sK2,sK2),u1_struct_0(sK0)) | ~spl3_12),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f168,f32])).
% 4.08/0.90  fof(f458,plain,(
% 4.08/0.90    ~spl3_22 | ~spl3_23 | ~spl3_24 | ~spl3_2 | ~spl3_3 | spl3_5),
% 4.08/0.90    inference(avatar_split_clause,[],[f101,f71,f47,f42,f455,f451,f447])).
% 4.08/0.90  fof(f455,plain,(
% 4.08/0.90    spl3_24 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 4.08/0.90  fof(f71,plain,(
% 4.08/0.90    spl3_5 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.08/0.90  fof(f101,plain,(
% 4.08/0.90    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | spl3_5)),
% 4.08/0.90    inference(forward_demodulation,[],[f90,f87])).
% 4.08/0.90  fof(f87,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f44,f35])).
% 4.08/0.90  fof(f90,plain,(
% 4.08/0.90    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 4.08/0.90    inference(superposition,[],[f73,f35])).
% 4.08/0.90  fof(f73,plain,(
% 4.08/0.90    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_5),
% 4.08/0.90    inference(avatar_component_clause,[],[f71])).
% 4.08/0.90  fof(f389,plain,(
% 4.08/0.90    spl3_21 | ~spl3_11),
% 4.08/0.90    inference(avatar_split_clause,[],[f214,f154,f386])).
% 4.08/0.90  fof(f386,plain,(
% 4.08/0.90    spl3_21 <=> r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 4.08/0.90  fof(f214,plain,(
% 4.08/0.90    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~spl3_11),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f156,f32])).
% 4.08/0.90  fof(f381,plain,(
% 4.08/0.90    ~spl3_20 | ~spl3_2 | ~spl3_3 | spl3_5),
% 4.08/0.90    inference(avatar_split_clause,[],[f98,f71,f47,f42,f378])).
% 4.08/0.90  fof(f98,plain,(
% 4.08/0.90    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | (~spl3_2 | ~spl3_3 | spl3_5)),
% 4.08/0.90    inference(backward_demodulation,[],[f75,f87])).
% 4.08/0.90  fof(f75,plain,(
% 4.08/0.90    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) | spl3_5),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f73,f32])).
% 4.08/0.90  fof(f350,plain,(
% 4.08/0.90    spl3_19 | ~spl3_10),
% 4.08/0.90    inference(avatar_split_clause,[],[f185,f149,f347])).
% 4.08/0.90  fof(f347,plain,(
% 4.08/0.90    spl3_19 <=> r1_tarski(k2_xboole_0(sK1,sK1),u1_struct_0(sK0))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 4.08/0.90  fof(f185,plain,(
% 4.08/0.90    r1_tarski(k2_xboole_0(sK1,sK1),u1_struct_0(sK0)) | ~spl3_10),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f151,f32])).
% 4.08/0.90  fof(f324,plain,(
% 4.08/0.90    spl3_18 | ~spl3_9),
% 4.08/0.90    inference(avatar_split_clause,[],[f138,f127,f321])).
% 4.08/0.90  fof(f321,plain,(
% 4.08/0.90    spl3_18 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 4.08/0.90  fof(f138,plain,(
% 4.08/0.90    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_9),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f129,f31])).
% 4.08/0.90  fof(f316,plain,(
% 4.08/0.90    spl3_17 | ~spl3_2 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f95,f47,f42,f313])).
% 4.08/0.90  fof(f313,plain,(
% 4.08/0.90    spl3_17 <=> k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 4.08/0.90  fof(f95,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 4.08/0.90    inference(forward_demodulation,[],[f88,f29])).
% 4.08/0.90  fof(f88,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f49,f35])).
% 4.08/0.90  fof(f311,plain,(
% 4.08/0.90    spl3_16 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f89,f47,f308])).
% 4.08/0.90  fof(f308,plain,(
% 4.08/0.90    spl3_16 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 4.08/0.90  fof(f89,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) | ~spl3_3),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f49,f35])).
% 4.08/0.90  fof(f306,plain,(
% 4.08/0.90    spl3_15 | ~spl3_8),
% 4.08/0.90    inference(avatar_split_clause,[],[f133,f122,f303])).
% 4.08/0.90  fof(f303,plain,(
% 4.08/0.90    spl3_15 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 4.08/0.90  fof(f133,plain,(
% 4.08/0.90    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2)) | ~spl3_8),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f124,f31])).
% 4.08/0.90  fof(f301,plain,(
% 4.08/0.90    spl3_14 | ~spl3_2 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f87,f47,f42,f298])).
% 4.08/0.90  fof(f298,plain,(
% 4.08/0.90    spl3_14 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 4.08/0.90  fof(f296,plain,(
% 4.08/0.90    spl3_13 | ~spl3_2),
% 4.08/0.90    inference(avatar_split_clause,[],[f86,f42,f293])).
% 4.08/0.90  fof(f293,plain,(
% 4.08/0.90    spl3_13 <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 4.08/0.90  fof(f86,plain,(
% 4.08/0.90    k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) | ~spl3_2),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f44,f35])).
% 4.08/0.90  fof(f169,plain,(
% 4.08/0.90    spl3_12 | ~spl3_2),
% 4.08/0.90    inference(avatar_split_clause,[],[f100,f42,f166])).
% 4.08/0.90  fof(f100,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.08/0.90    inference(backward_demodulation,[],[f82,f86])).
% 4.08/0.90  fof(f82,plain,(
% 4.08/0.90    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f44,f34])).
% 4.08/0.90  fof(f157,plain,(
% 4.08/0.90    spl3_11 | ~spl3_2 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f96,f47,f42,f154])).
% 4.08/0.90  fof(f96,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 4.08/0.90    inference(backward_demodulation,[],[f84,f95])).
% 4.08/0.90  fof(f84,plain,(
% 4.08/0.90    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f49,f34])).
% 4.08/0.90  fof(f152,plain,(
% 4.08/0.90    spl3_10 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f94,f47,f149])).
% 4.08/0.90  fof(f94,plain,(
% 4.08/0.90    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 4.08/0.90    inference(backward_demodulation,[],[f85,f89])).
% 4.08/0.90  fof(f85,plain,(
% 4.08/0.90    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f49,f34])).
% 4.08/0.90  fof(f130,plain,(
% 4.08/0.90    spl3_9 | ~spl3_1 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f68,f47,f37,f127])).
% 4.08/0.90  fof(f68,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_1 | ~spl3_3)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f49,f26])).
% 4.08/0.90  fof(f125,plain,(
% 4.08/0.90    spl3_8 | ~spl3_1 | ~spl3_2),
% 4.08/0.90    inference(avatar_split_clause,[],[f67,f42,f37,f122])).
% 4.08/0.90  fof(f67,plain,(
% 4.08/0.90    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_1 | ~spl3_2)),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f39,f44,f26])).
% 4.08/0.90  fof(f106,plain,(
% 4.08/0.90    ~spl3_7 | ~spl3_2 | ~spl3_3 | spl3_5),
% 4.08/0.90    inference(avatar_split_clause,[],[f99,f71,f47,f42,f103])).
% 4.08/0.90  fof(f103,plain,(
% 4.08/0.90    spl3_7 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.08/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 4.08/0.90  fof(f99,plain,(
% 4.08/0.90    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_5)),
% 4.08/0.90    inference(backward_demodulation,[],[f73,f87])).
% 4.08/0.90  fof(f81,plain,(
% 4.08/0.90    spl3_6 | ~spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f55,f47,f78])).
% 4.08/0.90  fof(f55,plain,(
% 4.08/0.90    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f49,f32])).
% 4.08/0.90  fof(f74,plain,(
% 4.08/0.90    ~spl3_5),
% 4.08/0.90    inference(avatar_split_clause,[],[f23,f71])).
% 4.08/0.90  fof(f23,plain,(
% 4.08/0.90    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 4.08/0.90    inference(cnf_transformation,[],[f12])).
% 4.08/0.90  fof(f12,plain,(
% 4.08/0.90    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.08/0.90    inference(ennf_transformation,[],[f11])).
% 4.08/0.90  fof(f11,negated_conjecture,(
% 4.08/0.90    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 4.08/0.90    inference(negated_conjecture,[],[f10])).
% 4.08/0.90  fof(f10,conjecture,(
% 4.08/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 4.08/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 4.08/0.90  fof(f63,plain,(
% 4.08/0.90    spl3_4 | ~spl3_2),
% 4.08/0.90    inference(avatar_split_clause,[],[f54,f42,f60])).
% 4.08/0.90  fof(f54,plain,(
% 4.08/0.90    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_2),
% 4.08/0.90    inference(unit_resulting_resolution,[],[f44,f32])).
% 4.08/0.90  fof(f50,plain,(
% 4.08/0.90    spl3_3),
% 4.08/0.90    inference(avatar_split_clause,[],[f24,f47])).
% 4.08/0.90  fof(f24,plain,(
% 4.08/0.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    inference(cnf_transformation,[],[f12])).
% 4.08/0.90  fof(f45,plain,(
% 4.08/0.90    spl3_2),
% 4.08/0.90    inference(avatar_split_clause,[],[f22,f42])).
% 4.08/0.90  fof(f22,plain,(
% 4.08/0.90    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.08/0.90    inference(cnf_transformation,[],[f12])).
% 4.08/0.90  fof(f40,plain,(
% 4.08/0.90    spl3_1),
% 4.08/0.90    inference(avatar_split_clause,[],[f25,f37])).
% 4.08/0.90  fof(f25,plain,(
% 4.08/0.90    l1_pre_topc(sK0)),
% 4.08/0.90    inference(cnf_transformation,[],[f12])).
% 4.08/0.90  % SZS output end Proof for theBenchmark
% 4.08/0.90  % (4915)------------------------------
% 4.08/0.90  % (4915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.90  % (4915)Termination reason: Refutation
% 4.08/0.90  
% 4.08/0.90  % (4915)Memory used [KB]: 3709
% 4.08/0.90  % (4915)Time elapsed: 0.484 s
% 4.08/0.90  % (4915)------------------------------
% 4.08/0.90  % (4915)------------------------------
% 4.08/0.90  % (4894)Success in time 0.554 s
%------------------------------------------------------------------------------
