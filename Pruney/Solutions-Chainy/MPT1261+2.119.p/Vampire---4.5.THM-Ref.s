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
% DateTime   : Thu Dec  3 13:12:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 342 expanded)
%              Number of leaves         :   55 ( 152 expanded)
%              Depth                    :   11
%              Number of atoms          :  598 (1109 expanded)
%              Number of equality atoms :  135 ( 251 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30526)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f958,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f99,f104,f108,f112,f127,f137,f147,f158,f185,f192,f196,f204,f209,f260,f270,f280,f317,f359,f403,f412,f510,f526,f567,f609,f668,f735,f744,f812,f898,f945,f957])).

fof(f957,plain,
    ( ~ spl2_21
    | spl2_80
    | ~ spl2_123 ),
    inference(avatar_contradiction_clause,[],[f956])).

fof(f956,plain,
    ( $false
    | ~ spl2_21
    | spl2_80
    | ~ spl2_123 ),
    inference(subsumption_resolution,[],[f953,f553])).

fof(f553,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_80 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl2_80
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f953,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_21
    | ~ spl2_123 ),
    inference(superposition,[],[f191,f944])).

fof(f944,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_123 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl2_123
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).

fof(f191,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl2_21
  <=> ! [X1,X0] : k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f945,plain,
    ( spl2_123
    | ~ spl2_16
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f899,f896,f155,f942])).

fof(f155,plain,
    ( spl2_16
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f896,plain,
    ( spl2_120
  <=> ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k7_subset_1(sK1,sK1,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f899,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_16
    | ~ spl2_120 ),
    inference(superposition,[],[f897,f157])).

fof(f157,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f897,plain,
    ( ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k7_subset_1(sK1,sK1,X9)
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f896])).

fof(f898,plain,
    ( spl2_120
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_107 ),
    inference(avatar_split_clause,[],[f886,f810,f101,f97,f896])).

fof(f97,plain,
    ( spl2_4
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f810,plain,
    ( spl2_107
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f886,plain,
    ( ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k7_subset_1(sK1,sK1,X9)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f882,f878])).

fof(f878,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1)
    | ~ spl2_4
    | ~ spl2_107 ),
    inference(resolution,[],[f811,f98])).

% (30527)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f98,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f811,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f810])).

fof(f882,plain,
    ( ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)))
    | ~ spl2_5
    | ~ spl2_107 ),
    inference(resolution,[],[f811,f103])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f812,plain,(
    spl2_107 ),
    inference(avatar_split_clause,[],[f80,f810])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f744,plain,
    ( ~ spl2_5
    | spl2_16
    | ~ spl2_35
    | ~ spl2_100 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl2_5
    | spl2_16
    | ~ spl2_35
    | ~ spl2_100 ),
    inference(subsumption_resolution,[],[f742,f156])).

fof(f156,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f742,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_35
    | ~ spl2_100 ),
    inference(forward_demodulation,[],[f740,f279])).

fof(f279,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl2_35
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f740,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_100 ),
    inference(resolution,[],[f734,f103])).

fof(f734,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f733])).

fof(f733,plain,
    ( spl2_100
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f735,plain,
    ( spl2_100
    | ~ spl2_2
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f731,f666,f88,f733])).

fof(f88,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f666,plain,
    ( spl2_89
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f731,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_89 ),
    inference(resolution,[],[f667,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f667,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f666])).

fof(f668,plain,(
    spl2_89 ),
    inference(avatar_split_clause,[],[f54,f666])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f609,plain,
    ( ~ spl2_16
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_22
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f584,f277,f194,f101,f88,f83,f155])).

fof(f83,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f194,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f584,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_22
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f50,f583])).

fof(f583,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_22
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f582,f85])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f582,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_22
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f581,f90])).

fof(f581,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_5
    | ~ spl2_22
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f570,f103])).

fof(f570,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_22
    | ~ spl2_35 ),
    inference(superposition,[],[f195,f279])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f567,plain,
    ( spl2_35
    | ~ spl2_5
    | ~ spl2_57
    | ~ spl2_77
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f562,f552,f524,f409,f101,f277])).

fof(f409,plain,
    ( spl2_57
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f524,plain,
    ( spl2_77
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f562,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_57
    | ~ spl2_77
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f530,f561])).

fof(f561,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_57
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f411,f554])).

fof(f554,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f552])).

fof(f411,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f409])).

fof(f530,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_77 ),
    inference(resolution,[],[f525,f103])).

fof(f525,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f524])).

fof(f526,plain,
    ( spl2_77
    | ~ spl2_2
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f522,f508,f88,f524])).

fof(f508,plain,
    ( spl2_74
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_74 ),
    inference(resolution,[],[f509,f90])).

fof(f509,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f508])).

fof(f510,plain,(
    spl2_74 ),
    inference(avatar_split_clause,[],[f53,f508])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f412,plain,
    ( spl2_57
    | ~ spl2_5
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f407,f401,f101,f409])).

fof(f401,plain,
    ( spl2_56
  <=> ! [X2] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f407,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_56 ),
    inference(resolution,[],[f402,f103])).

fof(f402,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) )
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f401])).

fof(f403,plain,
    ( spl2_56
    | ~ spl2_25
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f362,f357,f207,f401])).

fof(f207,plain,
    ( spl2_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f357,plain,
    ( spl2_49
  <=> ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X8) = k2_xboole_0(sK1,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f362,plain,
    ( ! [X2] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_25
    | ~ spl2_49 ),
    inference(resolution,[],[f358,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f207])).

fof(f358,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X8) = k2_xboole_0(sK1,X8) )
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,
    ( spl2_49
    | ~ spl2_5
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f355,f315,f101,f357])).

fof(f315,plain,
    ( spl2_42
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f355,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X8) = k2_xboole_0(sK1,X8) )
    | ~ spl2_5
    | ~ spl2_42 ),
    inference(resolution,[],[f316,f103])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f315])).

fof(f317,plain,(
    spl2_42 ),
    inference(avatar_split_clause,[],[f68,f315])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f280,plain,
    ( spl2_35
    | ~ spl2_5
    | ~ spl2_15
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f273,f268,f151,f101,f277])).

fof(f151,plain,
    ( spl2_15
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f268,plain,
    ( spl2_34
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f273,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_15
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f271,f103])).

fof(f271,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_15
    | ~ spl2_34 ),
    inference(resolution,[],[f269,f153])).

fof(f153,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f268])).

fof(f270,plain,
    ( spl2_34
    | ~ spl2_2
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f266,f258,f88,f268])).

fof(f258,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_32 ),
    inference(resolution,[],[f259,f90])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,(
    spl2_32 ),
    inference(avatar_split_clause,[],[f55,f258])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f209,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f205,f202,f88,f207])).

fof(f202,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_24 ),
    inference(resolution,[],[f203,f90])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f63,f202])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f196,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f62,f194])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f192,plain,
    ( spl2_21
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f186,f183,f97,f190])).

fof(f183,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,k7_subset_1(X1,X0,X2)) = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f186,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(resolution,[],[f184,f98])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(X1,k7_subset_1(X1,X0,X2)) = X1 )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl2_20
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f149,f145,f125,f106,f183])).

fof(f106,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f125,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f145,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(k7_subset_1(X1,X0,X2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,k7_subset_1(X1,X0,X2)) = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f148,f107])).

fof(f107,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k2_xboole_0(k7_subset_1(X1,X0,X2),X1) = X1 )
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(resolution,[],[f146,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_subset_1(X1,X0,X2),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f158,plain,
    ( spl2_15
    | spl2_16 ),
    inference(avatar_split_clause,[],[f49,f155,f151])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f147,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f143,f135,f110,f145])).

fof(f110,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f135,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(k7_subset_1(X1,X0,X2),X1) )
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(resolution,[],[f136,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f66,f135])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f127,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f61,f125])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f112,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f64,f110])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f104,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f81,f97])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f52,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f91,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (30528)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (30525)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (30537)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % (30529)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (30535)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (30524)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (30528)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  % (30526)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  fof(f958,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f86,f91,f99,f104,f108,f112,f127,f137,f147,f158,f185,f192,f196,f204,f209,f260,f270,f280,f317,f359,f403,f412,f510,f526,f567,f609,f668,f735,f744,f812,f898,f945,f957])).
% 0.21/0.47  fof(f957,plain,(
% 0.21/0.47    ~spl2_21 | spl2_80 | ~spl2_123),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f956])).
% 0.21/0.47  fof(f956,plain,(
% 0.21/0.47    $false | (~spl2_21 | spl2_80 | ~spl2_123)),
% 0.21/0.47    inference(subsumption_resolution,[],[f953,f553])).
% 0.21/0.47  fof(f553,plain,(
% 0.21/0.47    sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_80),
% 0.21/0.47    inference(avatar_component_clause,[],[f552])).
% 0.21/0.47  fof(f552,plain,(
% 0.21/0.47    spl2_80 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.21/0.47  fof(f953,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_21 | ~spl2_123)),
% 0.21/0.47    inference(superposition,[],[f191,f944])).
% 0.21/0.47  fof(f944,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_123),
% 0.21/0.47    inference(avatar_component_clause,[],[f942])).
% 0.21/0.47  fof(f942,plain,(
% 0.21/0.47    spl2_123 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0) ) | ~spl2_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f190])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl2_21 <=> ! [X1,X0] : k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.47  fof(f945,plain,(
% 0.21/0.47    spl2_123 | ~spl2_16 | ~spl2_120),
% 0.21/0.47    inference(avatar_split_clause,[],[f899,f896,f155,f942])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl2_16 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.47  fof(f896,plain,(
% 0.21/0.47    spl2_120 <=> ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k7_subset_1(sK1,sK1,X9)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 0.21/0.47  fof(f899,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_16 | ~spl2_120)),
% 0.21/0.47    inference(superposition,[],[f897,f157])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f155])).
% 0.21/0.47  fof(f897,plain,(
% 0.21/0.47    ( ! [X9] : (k7_subset_1(u1_struct_0(sK0),sK1,X9) = k7_subset_1(sK1,sK1,X9)) ) | ~spl2_120),
% 0.21/0.47    inference(avatar_component_clause,[],[f896])).
% 0.21/0.47  fof(f898,plain,(
% 0.21/0.47    spl2_120 | ~spl2_4 | ~spl2_5 | ~spl2_107),
% 0.21/0.47    inference(avatar_split_clause,[],[f886,f810,f101,f97,f896])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl2_4 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f810,plain,(
% 0.21/0.47    spl2_107 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 0.21/0.47  fof(f886,plain,(
% 0.21/0.47    ( ! [X9] : (k7_subset_1(u1_struct_0(sK0),sK1,X9) = k7_subset_1(sK1,sK1,X9)) ) | (~spl2_4 | ~spl2_5 | ~spl2_107)),
% 0.21/0.47    inference(forward_demodulation,[],[f882,f878])).
% 0.21/0.47  fof(f878,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1)) ) | (~spl2_4 | ~spl2_107)),
% 0.21/0.47    inference(resolution,[],[f811,f98])).
% 0.21/0.47  % (30527)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f97])).
% 0.21/0.47  fof(f811,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ) | ~spl2_107),
% 0.21/0.47    inference(avatar_component_clause,[],[f810])).
% 0.21/0.47  fof(f882,plain,(
% 0.21/0.47    ( ! [X9] : (k7_subset_1(u1_struct_0(sK0),sK1,X9) = k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)))) ) | (~spl2_5 | ~spl2_107)),
% 0.21/0.47    inference(resolution,[],[f811,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f812,plain,(
% 0.21/0.47    spl2_107),
% 0.21/0.47    inference(avatar_split_clause,[],[f80,f810])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f67,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f60,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f58,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f59,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f65,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f69,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f70,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f71,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.47  fof(f744,plain,(
% 0.21/0.47    ~spl2_5 | spl2_16 | ~spl2_35 | ~spl2_100),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f743])).
% 0.21/0.47  fof(f743,plain,(
% 0.21/0.47    $false | (~spl2_5 | spl2_16 | ~spl2_35 | ~spl2_100)),
% 0.21/0.47    inference(subsumption_resolution,[],[f742,f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f155])).
% 0.21/0.47  fof(f742,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_35 | ~spl2_100)),
% 0.21/0.47    inference(forward_demodulation,[],[f740,f279])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f277])).
% 0.21/0.47  fof(f277,plain,(
% 0.21/0.47    spl2_35 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.47  fof(f740,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_100)),
% 0.21/0.47    inference(resolution,[],[f734,f103])).
% 0.21/0.47  fof(f734,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_100),
% 0.21/0.47    inference(avatar_component_clause,[],[f733])).
% 0.21/0.47  fof(f733,plain,(
% 0.21/0.47    spl2_100 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 0.21/0.47  fof(f735,plain,(
% 0.21/0.47    spl2_100 | ~spl2_2 | ~spl2_89),
% 0.21/0.47    inference(avatar_split_clause,[],[f731,f666,f88,f733])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f666,plain,(
% 0.21/0.47    spl2_89 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 0.21/0.47  fof(f731,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_89)),
% 0.21/0.47    inference(resolution,[],[f667,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f667,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_89),
% 0.21/0.47    inference(avatar_component_clause,[],[f666])).
% 0.21/0.47  fof(f668,plain,(
% 0.21/0.47    spl2_89),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f666])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.47  fof(f609,plain,(
% 0.21/0.47    ~spl2_16 | ~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_22 | ~spl2_35),
% 0.21/0.47    inference(avatar_split_clause,[],[f584,f277,f194,f101,f88,f83,f155])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    spl2_22 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.47  fof(f584,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_22 | ~spl2_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f583])).
% 0.21/0.47  fof(f583,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_22 | ~spl2_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f582,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f582,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_5 | ~spl2_22 | ~spl2_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f581,f90])).
% 0.21/0.47  fof(f581,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_5 | ~spl2_22 | ~spl2_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f570,f103])).
% 0.21/0.47  fof(f570,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_22 | ~spl2_35)),
% 0.21/0.47    inference(superposition,[],[f195,f279])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f194])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f22])).
% 0.21/0.47  fof(f22,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.47  fof(f567,plain,(
% 0.21/0.47    spl2_35 | ~spl2_5 | ~spl2_57 | ~spl2_77 | ~spl2_80),
% 0.21/0.47    inference(avatar_split_clause,[],[f562,f552,f524,f409,f101,f277])).
% 0.21/0.47  fof(f409,plain,(
% 0.21/0.47    spl2_57 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.21/0.47  fof(f524,plain,(
% 0.21/0.47    spl2_77 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 0.21/0.47  fof(f562,plain,(
% 0.21/0.47    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_5 | ~spl2_57 | ~spl2_77 | ~spl2_80)),
% 0.21/0.47    inference(forward_demodulation,[],[f530,f561])).
% 0.21/0.47  fof(f561,plain,(
% 0.21/0.47    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_57 | ~spl2_80)),
% 0.21/0.47    inference(forward_demodulation,[],[f411,f554])).
% 0.21/0.47  fof(f554,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_80),
% 0.21/0.47    inference(avatar_component_clause,[],[f552])).
% 0.21/0.47  fof(f411,plain,(
% 0.21/0.47    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_57),
% 0.21/0.47    inference(avatar_component_clause,[],[f409])).
% 0.21/0.47  fof(f530,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_77)),
% 0.21/0.47    inference(resolution,[],[f525,f103])).
% 0.21/0.47  fof(f525,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_77),
% 0.21/0.47    inference(avatar_component_clause,[],[f524])).
% 0.21/0.47  fof(f526,plain,(
% 0.21/0.47    spl2_77 | ~spl2_2 | ~spl2_74),
% 0.21/0.47    inference(avatar_split_clause,[],[f522,f508,f88,f524])).
% 0.21/0.47  fof(f508,plain,(
% 0.21/0.47    spl2_74 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 0.21/0.47  fof(f522,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_74)),
% 0.21/0.47    inference(resolution,[],[f509,f90])).
% 0.21/0.47  fof(f509,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_74),
% 0.21/0.47    inference(avatar_component_clause,[],[f508])).
% 0.21/0.47  fof(f510,plain,(
% 0.21/0.47    spl2_74),
% 0.21/0.47    inference(avatar_split_clause,[],[f53,f508])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.47  fof(f412,plain,(
% 0.21/0.47    spl2_57 | ~spl2_5 | ~spl2_56),
% 0.21/0.47    inference(avatar_split_clause,[],[f407,f401,f101,f409])).
% 0.21/0.47  fof(f401,plain,(
% 0.21/0.47    spl2_56 <=> ! [X2] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.21/0.47  fof(f407,plain,(
% 0.21/0.47    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_56)),
% 0.21/0.47    inference(resolution,[],[f402,f103])).
% 0.21/0.47  fof(f402,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))) ) | ~spl2_56),
% 0.21/0.47    inference(avatar_component_clause,[],[f401])).
% 0.21/0.47  fof(f403,plain,(
% 0.21/0.47    spl2_56 | ~spl2_25 | ~spl2_49),
% 0.21/0.47    inference(avatar_split_clause,[],[f362,f357,f207,f401])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    spl2_25 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.47  fof(f357,plain,(
% 0.21/0.47    spl2_49 <=> ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X8) = k2_xboole_0(sK1,X8))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.47  fof(f362,plain,(
% 0.21/0.47    ( ! [X2] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_25 | ~spl2_49)),
% 0.21/0.47    inference(resolution,[],[f358,f208])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f207])).
% 0.21/0.47  fof(f358,plain,(
% 0.21/0.47    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X8) = k2_xboole_0(sK1,X8)) ) | ~spl2_49),
% 0.21/0.47    inference(avatar_component_clause,[],[f357])).
% 0.21/0.47  fof(f359,plain,(
% 0.21/0.47    spl2_49 | ~spl2_5 | ~spl2_42),
% 0.21/0.47    inference(avatar_split_clause,[],[f355,f315,f101,f357])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    spl2_42 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.47  fof(f355,plain,(
% 0.21/0.47    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X8) = k2_xboole_0(sK1,X8)) ) | (~spl2_5 | ~spl2_42)),
% 0.21/0.47    inference(resolution,[],[f316,f103])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) ) | ~spl2_42),
% 0.21/0.47    inference(avatar_component_clause,[],[f315])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    spl2_42),
% 0.21/0.47    inference(avatar_split_clause,[],[f68,f315])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    spl2_35 | ~spl2_5 | ~spl2_15 | ~spl2_34),
% 0.21/0.47    inference(avatar_split_clause,[],[f273,f268,f151,f101,f277])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl2_15 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    spl2_34 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_5 | ~spl2_15 | ~spl2_34)),
% 0.21/0.47    inference(subsumption_resolution,[],[f271,f103])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_15 | ~spl2_34)),
% 0.21/0.47    inference(resolution,[],[f269,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f151])).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f268])).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    spl2_34 | ~spl2_2 | ~spl2_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f266,f258,f88,f268])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    spl2_32 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_32)),
% 0.21/0.47    inference(resolution,[],[f259,f90])).
% 0.21/0.47  fof(f259,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f258])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    spl2_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f258])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    spl2_25 | ~spl2_2 | ~spl2_24),
% 0.21/0.47    inference(avatar_split_clause,[],[f205,f202,f88,f207])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    spl2_24 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_24)),
% 0.21/0.47    inference(resolution,[],[f203,f90])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f202])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    spl2_24),
% 0.21/0.47    inference(avatar_split_clause,[],[f63,f202])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    spl2_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f194])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    spl2_21 | ~spl2_4 | ~spl2_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f186,f183,f97,f190])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    spl2_20 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,k7_subset_1(X1,X0,X2)) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0) ) | (~spl2_4 | ~spl2_20)),
% 0.21/0.47    inference(resolution,[],[f184,f98])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X1,k7_subset_1(X1,X0,X2)) = X1) ) | ~spl2_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f183])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    spl2_20 | ~spl2_6 | ~spl2_10 | ~spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f149,f145,f125,f106,f183])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl2_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl2_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k7_subset_1(X1,X0,X2),X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k7_subset_1(X1,X0,X2)) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | (~spl2_6 | ~spl2_10 | ~spl2_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f148,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(k7_subset_1(X1,X0,X2),X1) = X1) ) | (~spl2_10 | ~spl2_14)),
% 0.21/0.47    inference(resolution,[],[f146,f126])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(X1,X0,X2),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f145])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl2_15 | spl2_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f49,f155,f151])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    spl2_14 | ~spl2_7 | ~spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f143,f135,f110,f145])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl2_12 <=> ! [X1,X0,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k7_subset_1(X1,X0,X2),X1)) ) | (~spl2_7 | ~spl2_12)),
% 0.21/0.47    inference(resolution,[],[f136,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f66,f135])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f125])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f110])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f106])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f81,f97])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f52,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f88])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f83])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30528)------------------------------
% 0.21/0.47  % (30528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30528)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30528)Memory used [KB]: 6908
% 0.21/0.47  % (30528)Time elapsed: 0.062 s
% 0.21/0.47  % (30528)------------------------------
% 0.21/0.47  % (30528)------------------------------
% 0.21/0.47  % (30520)Success in time 0.12 s
%------------------------------------------------------------------------------
