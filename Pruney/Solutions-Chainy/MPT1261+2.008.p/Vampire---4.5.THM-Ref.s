%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:48 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 313 expanded)
%              Number of leaves         :   39 ( 120 expanded)
%              Depth                    :   11
%              Number of atoms          :  494 ( 957 expanded)
%              Number of equality atoms :  112 ( 233 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f113,f118,f123,f128,f246,f282,f322,f798,f805,f831,f841,f1040,f1112,f1268,f1300,f1308,f1323,f1468,f1478])).

fof(f1478,plain,
    ( ~ spl2_15
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f1477])).

fof(f1477,plain,
    ( $false
    | ~ spl2_15
    | spl2_18 ),
    inference(subsumption_resolution,[],[f1475,f279])).

fof(f279,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl2_15
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f1475,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_18 ),
    inference(resolution,[],[f320,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f320,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl2_18
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f1468,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_37 ),
    inference(avatar_contradiction_clause,[],[f1467])).

fof(f1467,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_37 ),
    inference(subsumption_resolution,[],[f1466,f122])).

fof(f122,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1466,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_37 ),
    inference(subsumption_resolution,[],[f1464,f117])).

fof(f117,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1464,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_37 ),
    inference(trivial_inequality_removal,[],[f1462])).

fof(f1462,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_37 ),
    inference(superposition,[],[f1016,f355])).

fof(f355,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1016,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_37 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1015,plain,
    ( spl2_37
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1323,plain,
    ( ~ spl2_11
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1322,f115,f109,f217])).

fof(f217,plain,
    ( spl2_11
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f109,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1322,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1321,f117])).

fof(f1321,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f111,f76])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1308,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f1307,f1210,f120,f115,f325])).

fof(f325,plain,
    ( spl2_19
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1210,plain,
    ( spl2_50
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f1307,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f1306,f122])).

fof(f1306,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f1279,f117])).

fof(f1279,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_50 ),
    inference(superposition,[],[f1212,f366])).

fof(f366,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f363,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f363,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f81,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1212,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1300,plain,
    ( spl2_11
    | ~ spl2_30
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f1299,f1021,f824,f217])).

fof(f824,plain,
    ( spl2_30
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1021,plain,
    ( spl2_38
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f1299,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_30
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f1153,f825])).

fof(f825,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f824])).

fof(f1153,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_38 ),
    inference(superposition,[],[f1023,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1023,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1268,plain,
    ( spl2_50
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f1260,f1037,f1210])).

fof(f1037,plain,
    ( spl2_40
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1260,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(superposition,[],[f1214,f1039])).

fof(f1039,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1214,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(backward_demodulation,[],[f180,f450])).

fof(f450,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f446,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f446,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f91,f177])).

fof(f177,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f94,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f180,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f91,f94])).

fof(f1112,plain,
    ( spl2_38
    | ~ spl2_18
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1111,f1015,f319,f1021])).

fof(f1111,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f1094,f321])).

fof(f321,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1094,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f198,f1017])).

fof(f1017,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f198,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f72,f73])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1040,plain,
    ( spl2_40
    | ~ spl2_18
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f1035,f828,f319,f1037])).

fof(f828,plain,
    ( spl2_31
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1035,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f1012,f321])).

fof(f1012,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_31 ),
    inference(superposition,[],[f303,f830])).

fof(f830,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f828])).

fof(f303,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f302,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f302,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f96,f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f89,f99])).

fof(f99,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f841,plain,
    ( ~ spl2_12
    | spl2_30 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl2_12
    | spl2_30 ),
    inference(subsumption_resolution,[],[f838,f245])).

fof(f245,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl2_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f838,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_30 ),
    inference(resolution,[],[f826,f85])).

fof(f826,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f824])).

fof(f831,plain,
    ( ~ spl2_30
    | spl2_31
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f817,f217,f828,f824])).

fof(f817,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_11 ),
    inference(superposition,[],[f198,f219])).

fof(f219,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f217])).

fof(f805,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f804,f115,f109,f217])).

fof(f804,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f801,f117])).

fof(f801,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f76,f110])).

fof(f110,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f798,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f797,f325,f125,f120,f115,f105])).

fof(f105,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f125,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f797,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f796,f122])).

fof(f796,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f795,f117])).

fof(f795,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f399,f127])).

fof(f127,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f399,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_19 ),
    inference(trivial_inequality_removal,[],[f398])).

fof(f398,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_19 ),
    inference(superposition,[],[f83,f327])).

fof(f327,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f325])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f322,plain,
    ( spl2_18
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f307,f217,f319])).

fof(f307,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_11 ),
    inference(superposition,[],[f138,f219])).

fof(f138,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f101,f93])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f101,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f282,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f281,f120,f115,f105,f277])).

fof(f281,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f272,f122])).

fof(f272,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f80,f117])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f246,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f241,f120,f115,f243])).

fof(f241,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f240,f122])).

fof(f240,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f78,f117])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f128,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f64,f125])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f58,plain,
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

fof(f59,plain,
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

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f123,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f65,f120])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f118,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f66,f115])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f67,f109,f105])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f112,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f68,f109,f105])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (13585)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (13577)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (13582)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (13605)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (13581)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (13579)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (13580)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (13597)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (13598)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (13599)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (13576)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (13590)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (13591)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (13589)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (13604)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (13586)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (13602)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (13603)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (13583)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (13592)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (13596)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (13600)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (13584)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (13578)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.55  % (13595)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (13594)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (13601)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (13588)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (13587)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.57  % (13593)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.04/0.63  % (13597)Refutation found. Thanks to Tanya!
% 2.04/0.63  % SZS status Theorem for theBenchmark
% 2.04/0.63  % SZS output start Proof for theBenchmark
% 2.04/0.63  fof(f1479,plain,(
% 2.04/0.63    $false),
% 2.04/0.63    inference(avatar_sat_refutation,[],[f112,f113,f118,f123,f128,f246,f282,f322,f798,f805,f831,f841,f1040,f1112,f1268,f1300,f1308,f1323,f1468,f1478])).
% 2.04/0.63  fof(f1478,plain,(
% 2.04/0.63    ~spl2_15 | spl2_18),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f1477])).
% 2.04/0.63  fof(f1477,plain,(
% 2.04/0.63    $false | (~spl2_15 | spl2_18)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1475,f279])).
% 2.04/0.63  fof(f279,plain,(
% 2.04/0.63    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_15),
% 2.04/0.63    inference(avatar_component_clause,[],[f277])).
% 2.04/0.63  fof(f277,plain,(
% 2.04/0.63    spl2_15 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.04/0.63  fof(f1475,plain,(
% 2.04/0.63    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_18),
% 2.04/0.63    inference(resolution,[],[f320,f85])).
% 2.04/0.63  fof(f85,plain,(
% 2.04/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f63])).
% 2.04/0.63  fof(f63,plain,(
% 2.04/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.04/0.63    inference(nnf_transformation,[],[f24])).
% 2.04/0.63  fof(f24,axiom,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.04/0.63  fof(f320,plain,(
% 2.04/0.63    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_18),
% 2.04/0.63    inference(avatar_component_clause,[],[f319])).
% 2.04/0.63  fof(f319,plain,(
% 2.04/0.63    spl2_18 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.04/0.63  fof(f1468,plain,(
% 2.04/0.63    ~spl2_3 | ~spl2_4 | spl2_37),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f1467])).
% 2.04/0.63  fof(f1467,plain,(
% 2.04/0.63    $false | (~spl2_3 | ~spl2_4 | spl2_37)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1466,f122])).
% 2.04/0.63  fof(f122,plain,(
% 2.04/0.63    l1_pre_topc(sK0) | ~spl2_4),
% 2.04/0.63    inference(avatar_component_clause,[],[f120])).
% 2.04/0.63  fof(f120,plain,(
% 2.04/0.63    spl2_4 <=> l1_pre_topc(sK0)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.04/0.63  fof(f1466,plain,(
% 2.04/0.63    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_37)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1464,f117])).
% 2.04/0.63  fof(f117,plain,(
% 2.04/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.04/0.63    inference(avatar_component_clause,[],[f115])).
% 2.04/0.63  fof(f115,plain,(
% 2.04/0.63    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.04/0.63  fof(f1464,plain,(
% 2.04/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_37),
% 2.04/0.63    inference(trivial_inequality_removal,[],[f1462])).
% 2.04/0.63  fof(f1462,plain,(
% 2.04/0.63    k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_37),
% 2.04/0.63    inference(superposition,[],[f1016,f355])).
% 2.04/0.63  fof(f355,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f354])).
% 2.04/0.63  fof(f354,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(superposition,[],[f76,f77])).
% 2.04/0.63  fof(f77,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f41])).
% 2.04/0.63  fof(f41,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f31])).
% 2.04/0.63  fof(f31,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.04/0.63  fof(f76,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f40])).
% 2.04/0.63  fof(f40,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f21])).
% 2.04/0.63  fof(f21,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.04/0.63  fof(f1016,plain,(
% 2.04/0.63    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_37),
% 2.04/0.63    inference(avatar_component_clause,[],[f1015])).
% 2.04/0.63  fof(f1015,plain,(
% 2.04/0.63    spl2_37 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 2.04/0.63  fof(f1323,plain,(
% 2.04/0.63    ~spl2_11 | spl2_2 | ~spl2_3),
% 2.04/0.63    inference(avatar_split_clause,[],[f1322,f115,f109,f217])).
% 2.04/0.63  fof(f217,plain,(
% 2.04/0.63    spl2_11 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.04/0.63  fof(f109,plain,(
% 2.04/0.63    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.04/0.63  fof(f1322,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1321,f117])).
% 2.04/0.63  fof(f1321,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 2.04/0.63    inference(superposition,[],[f111,f76])).
% 2.04/0.63  fof(f111,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.04/0.63    inference(avatar_component_clause,[],[f109])).
% 2.04/0.63  fof(f1308,plain,(
% 2.04/0.63    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_50),
% 2.04/0.63    inference(avatar_split_clause,[],[f1307,f1210,f120,f115,f325])).
% 2.04/0.63  fof(f325,plain,(
% 2.04/0.63    spl2_19 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.04/0.63  fof(f1210,plain,(
% 2.04/0.63    spl2_50 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 2.04/0.63  fof(f1307,plain,(
% 2.04/0.63    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_50)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1306,f122])).
% 2.04/0.63  fof(f1306,plain,(
% 2.04/0.63    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_50)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1279,f117])).
% 2.04/0.63  fof(f1279,plain,(
% 2.04/0.63    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_50),
% 2.04/0.63    inference(superposition,[],[f1212,f366])).
% 2.04/0.63  fof(f366,plain,(
% 2.04/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.04/0.63    inference(subsumption_resolution,[],[f363,f79])).
% 2.04/0.63  fof(f79,plain,(
% 2.04/0.63    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f44])).
% 2.04/0.63  fof(f44,plain,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f43])).
% 2.04/0.63  fof(f43,plain,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f26])).
% 2.04/0.63  fof(f26,axiom,(
% 2.04/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.04/0.63  fof(f363,plain,(
% 2.04/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f360])).
% 2.04/0.63  fof(f360,plain,(
% 2.04/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.04/0.63    inference(superposition,[],[f81,f96])).
% 2.04/0.63  fof(f96,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f55])).
% 2.04/0.63  fof(f55,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(flattening,[],[f54])).
% 2.04/0.63  fof(f54,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.04/0.63    inference(ennf_transformation,[],[f19])).
% 2.04/0.63  fof(f19,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.04/0.63  fof(f81,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f47])).
% 2.04/0.63  fof(f47,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f29])).
% 2.04/0.63  fof(f29,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.04/0.63  fof(f1212,plain,(
% 2.04/0.63    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_50),
% 2.04/0.63    inference(avatar_component_clause,[],[f1210])).
% 2.04/0.63  fof(f1300,plain,(
% 2.04/0.63    spl2_11 | ~spl2_30 | ~spl2_38),
% 2.04/0.63    inference(avatar_split_clause,[],[f1299,f1021,f824,f217])).
% 2.04/0.63  fof(f824,plain,(
% 2.04/0.63    spl2_30 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 2.04/0.63  fof(f1021,plain,(
% 2.04/0.63    spl2_38 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 2.04/0.63  fof(f1299,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_30 | ~spl2_38)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1153,f825])).
% 2.04/0.63  fof(f825,plain,(
% 2.04/0.63    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_30),
% 2.04/0.63    inference(avatar_component_clause,[],[f824])).
% 2.04/0.63  fof(f1153,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_38),
% 2.04/0.63    inference(superposition,[],[f1023,f73])).
% 2.04/0.63  fof(f73,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f37])).
% 2.04/0.63  fof(f37,plain,(
% 2.04/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f15])).
% 2.04/0.63  fof(f15,axiom,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.04/0.63  fof(f1023,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_38),
% 2.04/0.63    inference(avatar_component_clause,[],[f1021])).
% 2.04/0.63  fof(f1268,plain,(
% 2.04/0.63    spl2_50 | ~spl2_40),
% 2.04/0.63    inference(avatar_split_clause,[],[f1260,f1037,f1210])).
% 2.04/0.63  fof(f1037,plain,(
% 2.04/0.63    spl2_40 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 2.04/0.63  fof(f1260,plain,(
% 2.04/0.63    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_40),
% 2.04/0.63    inference(superposition,[],[f1214,f1039])).
% 2.04/0.63  fof(f1039,plain,(
% 2.04/0.63    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_40),
% 2.04/0.63    inference(avatar_component_clause,[],[f1037])).
% 2.04/0.63  fof(f1214,plain,(
% 2.04/0.63    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 2.04/0.63    inference(backward_demodulation,[],[f180,f450])).
% 2.04/0.63  fof(f450,plain,(
% 2.04/0.63    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.04/0.63    inference(forward_demodulation,[],[f446,f97])).
% 2.04/0.63  fof(f97,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.04/0.63    inference(cnf_transformation,[],[f6])).
% 2.04/0.63  fof(f6,axiom,(
% 2.04/0.63    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.04/0.63  fof(f446,plain,(
% 2.04/0.63    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k1_xboole_0)) )),
% 2.04/0.63    inference(superposition,[],[f91,f177])).
% 2.04/0.63  fof(f177,plain,(
% 2.04/0.63    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 2.04/0.63    inference(superposition,[],[f94,f90])).
% 2.04/0.63  fof(f90,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.04/0.63    inference(cnf_transformation,[],[f9])).
% 2.04/0.63  fof(f9,axiom,(
% 2.04/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.04/0.63  fof(f94,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f8])).
% 2.04/0.63  fof(f8,axiom,(
% 2.04/0.63    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.04/0.63  fof(f91,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f11])).
% 2.04/0.63  fof(f11,axiom,(
% 2.04/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.04/0.63  fof(f180,plain,(
% 2.04/0.63    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 2.04/0.63    inference(superposition,[],[f91,f94])).
% 2.04/0.63  fof(f1112,plain,(
% 2.04/0.63    spl2_38 | ~spl2_18 | ~spl2_37),
% 2.04/0.63    inference(avatar_split_clause,[],[f1111,f1015,f319,f1021])).
% 2.04/0.63  fof(f1111,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_37)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1094,f321])).
% 2.04/0.63  fof(f321,plain,(
% 2.04/0.63    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_18),
% 2.04/0.63    inference(avatar_component_clause,[],[f319])).
% 2.04/0.63  fof(f1094,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_37),
% 2.04/0.63    inference(superposition,[],[f198,f1017])).
% 2.04/0.63  fof(f1017,plain,(
% 2.04/0.63    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_37),
% 2.04/0.63    inference(avatar_component_clause,[],[f1015])).
% 2.04/0.63  fof(f198,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f194])).
% 2.04/0.63  fof(f194,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(superposition,[],[f72,f73])).
% 2.04/0.63  fof(f72,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f36])).
% 2.04/0.63  fof(f36,plain,(
% 2.04/0.63    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f18])).
% 2.04/0.63  fof(f18,axiom,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.04/0.63  fof(f1040,plain,(
% 2.04/0.63    spl2_40 | ~spl2_18 | ~spl2_31),
% 2.04/0.63    inference(avatar_split_clause,[],[f1035,f828,f319,f1037])).
% 2.04/0.63  fof(f828,plain,(
% 2.04/0.63    spl2_31 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.04/0.63  fof(f1035,plain,(
% 2.04/0.63    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_31)),
% 2.04/0.63    inference(subsumption_resolution,[],[f1012,f321])).
% 2.04/0.63  fof(f1012,plain,(
% 2.04/0.63    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_31),
% 2.04/0.63    inference(superposition,[],[f303,f830])).
% 2.04/0.63  fof(f830,plain,(
% 2.04/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_31),
% 2.04/0.63    inference(avatar_component_clause,[],[f828])).
% 2.04/0.63  fof(f303,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(subsumption_resolution,[],[f302,f86])).
% 2.04/0.63  fof(f86,plain,(
% 2.04/0.63    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f50])).
% 2.04/0.63  fof(f50,plain,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f16])).
% 2.04/0.63  fof(f16,axiom,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.04/0.63  fof(f302,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f299])).
% 2.04/0.63  fof(f299,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(superposition,[],[f96,f247])).
% 2.04/0.63  fof(f247,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(forward_demodulation,[],[f89,f99])).
% 2.04/0.63  fof(f99,plain,(
% 2.04/0.63    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.04/0.63    inference(cnf_transformation,[],[f14])).
% 2.04/0.63  fof(f14,axiom,(
% 2.04/0.63    ! [X0] : k2_subset_1(X0) = X0),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.04/0.63  fof(f89,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f53])).
% 2.04/0.63  fof(f53,plain,(
% 2.04/0.63    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f22])).
% 2.04/0.63  fof(f22,axiom,(
% 2.04/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 2.04/0.63  fof(f841,plain,(
% 2.04/0.63    ~spl2_12 | spl2_30),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f840])).
% 2.04/0.63  fof(f840,plain,(
% 2.04/0.63    $false | (~spl2_12 | spl2_30)),
% 2.04/0.63    inference(subsumption_resolution,[],[f838,f245])).
% 2.04/0.63  fof(f245,plain,(
% 2.04/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_12),
% 2.04/0.63    inference(avatar_component_clause,[],[f243])).
% 2.04/0.63  fof(f243,plain,(
% 2.04/0.63    spl2_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.04/0.63  fof(f838,plain,(
% 2.04/0.63    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_30),
% 2.04/0.63    inference(resolution,[],[f826,f85])).
% 2.04/0.63  fof(f826,plain,(
% 2.04/0.63    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_30),
% 2.04/0.63    inference(avatar_component_clause,[],[f824])).
% 2.04/0.63  fof(f831,plain,(
% 2.04/0.63    ~spl2_30 | spl2_31 | ~spl2_11),
% 2.04/0.63    inference(avatar_split_clause,[],[f817,f217,f828,f824])).
% 2.04/0.63  fof(f817,plain,(
% 2.04/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_11),
% 2.04/0.63    inference(superposition,[],[f198,f219])).
% 2.04/0.63  fof(f219,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_11),
% 2.04/0.63    inference(avatar_component_clause,[],[f217])).
% 2.04/0.63  fof(f805,plain,(
% 2.04/0.63    spl2_11 | ~spl2_2 | ~spl2_3),
% 2.04/0.63    inference(avatar_split_clause,[],[f804,f115,f109,f217])).
% 2.04/0.63  fof(f804,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.04/0.63    inference(subsumption_resolution,[],[f801,f117])).
% 2.04/0.63  fof(f801,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.04/0.63    inference(superposition,[],[f76,f110])).
% 2.04/0.63  fof(f110,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.04/0.63    inference(avatar_component_clause,[],[f109])).
% 2.04/0.63  fof(f798,plain,(
% 2.04/0.63    spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_19),
% 2.04/0.63    inference(avatar_split_clause,[],[f797,f325,f125,f120,f115,f105])).
% 2.04/0.63  fof(f105,plain,(
% 2.04/0.63    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.04/0.63  fof(f125,plain,(
% 2.04/0.63    spl2_5 <=> v2_pre_topc(sK0)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.04/0.63  fof(f797,plain,(
% 2.04/0.63    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_19)),
% 2.04/0.63    inference(subsumption_resolution,[],[f796,f122])).
% 2.04/0.63  fof(f796,plain,(
% 2.04/0.63    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_19)),
% 2.04/0.63    inference(subsumption_resolution,[],[f795,f117])).
% 2.04/0.63  fof(f795,plain,(
% 2.04/0.63    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_5 | ~spl2_19)),
% 2.04/0.63    inference(subsumption_resolution,[],[f399,f127])).
% 2.04/0.63  fof(f127,plain,(
% 2.04/0.63    v2_pre_topc(sK0) | ~spl2_5),
% 2.04/0.63    inference(avatar_component_clause,[],[f125])).
% 2.04/0.63  fof(f399,plain,(
% 2.04/0.63    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_19),
% 2.04/0.63    inference(trivial_inequality_removal,[],[f398])).
% 2.04/0.63  fof(f398,plain,(
% 2.04/0.63    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_19),
% 2.04/0.63    inference(superposition,[],[f83,f327])).
% 2.04/0.63  fof(f327,plain,(
% 2.04/0.63    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_19),
% 2.04/0.63    inference(avatar_component_clause,[],[f325])).
% 2.04/0.63  fof(f83,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f49])).
% 2.04/0.63  fof(f49,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f48])).
% 2.04/0.63  fof(f48,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f25])).
% 2.04/0.63  fof(f25,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.04/0.63  fof(f322,plain,(
% 2.04/0.63    spl2_18 | ~spl2_11),
% 2.04/0.63    inference(avatar_split_clause,[],[f307,f217,f319])).
% 2.04/0.63  fof(f307,plain,(
% 2.04/0.63    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_11),
% 2.04/0.63    inference(superposition,[],[f138,f219])).
% 2.04/0.63  fof(f138,plain,(
% 2.04/0.63    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(backward_demodulation,[],[f101,f93])).
% 2.04/0.63  fof(f93,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f20])).
% 2.04/0.63  fof(f20,axiom,(
% 2.04/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.04/0.63  fof(f101,plain,(
% 2.04/0.63    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f17])).
% 2.04/0.63  fof(f17,axiom,(
% 2.04/0.63    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.04/0.63  fof(f282,plain,(
% 2.04/0.63    spl2_15 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 2.04/0.63    inference(avatar_split_clause,[],[f281,f120,f115,f105,f277])).
% 2.04/0.63  fof(f281,plain,(
% 2.04/0.63    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 2.04/0.63    inference(subsumption_resolution,[],[f272,f122])).
% 2.04/0.63  fof(f272,plain,(
% 2.04/0.63    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.04/0.63    inference(resolution,[],[f80,f117])).
% 2.04/0.63  fof(f80,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f46])).
% 2.04/0.63  fof(f46,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f45])).
% 2.04/0.63  fof(f45,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f30])).
% 2.04/0.63  fof(f30,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.04/0.63  fof(f246,plain,(
% 2.04/0.63    spl2_12 | ~spl2_3 | ~spl2_4),
% 2.04/0.63    inference(avatar_split_clause,[],[f241,f120,f115,f243])).
% 2.04/0.63  fof(f241,plain,(
% 2.04/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 2.04/0.63    inference(subsumption_resolution,[],[f240,f122])).
% 2.04/0.63  fof(f240,plain,(
% 2.04/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.04/0.63    inference(resolution,[],[f78,f117])).
% 2.04/0.63  fof(f78,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f42])).
% 2.04/0.63  fof(f42,plain,(
% 2.04/0.63    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f27])).
% 2.04/0.63  fof(f27,axiom,(
% 2.04/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.04/0.63  fof(f128,plain,(
% 2.04/0.63    spl2_5),
% 2.04/0.63    inference(avatar_split_clause,[],[f64,f125])).
% 2.04/0.63  fof(f64,plain,(
% 2.04/0.63    v2_pre_topc(sK0)),
% 2.04/0.63    inference(cnf_transformation,[],[f60])).
% 2.04/0.63  fof(f60,plain,(
% 2.04/0.63    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 2.04/0.63  fof(f58,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f59,plain,(
% 2.04/0.63    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f57,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f56])).
% 2.04/0.63  fof(f56,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.63    inference(nnf_transformation,[],[f35])).
% 2.04/0.63  fof(f35,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.63    inference(flattening,[],[f34])).
% 2.04/0.63  fof(f34,plain,(
% 2.04/0.63    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f33])).
% 2.04/0.63  fof(f33,negated_conjecture,(
% 2.04/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.04/0.63    inference(negated_conjecture,[],[f32])).
% 2.04/0.63  fof(f32,conjecture,(
% 2.04/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.04/0.63  fof(f123,plain,(
% 2.04/0.63    spl2_4),
% 2.04/0.63    inference(avatar_split_clause,[],[f65,f120])).
% 2.04/0.63  fof(f65,plain,(
% 2.04/0.63    l1_pre_topc(sK0)),
% 2.04/0.63    inference(cnf_transformation,[],[f60])).
% 2.04/0.63  fof(f118,plain,(
% 2.04/0.63    spl2_3),
% 2.04/0.63    inference(avatar_split_clause,[],[f66,f115])).
% 2.04/0.63  fof(f66,plain,(
% 2.04/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.63    inference(cnf_transformation,[],[f60])).
% 2.04/0.63  fof(f113,plain,(
% 2.04/0.63    spl2_1 | spl2_2),
% 2.04/0.63    inference(avatar_split_clause,[],[f67,f109,f105])).
% 2.04/0.63  fof(f67,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.04/0.63    inference(cnf_transformation,[],[f60])).
% 2.04/0.63  fof(f112,plain,(
% 2.04/0.63    ~spl2_1 | ~spl2_2),
% 2.04/0.63    inference(avatar_split_clause,[],[f68,f109,f105])).
% 2.04/0.63  fof(f68,plain,(
% 2.04/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.04/0.63    inference(cnf_transformation,[],[f60])).
% 2.04/0.63  % SZS output end Proof for theBenchmark
% 2.04/0.63  % (13597)------------------------------
% 2.04/0.63  % (13597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (13597)Termination reason: Refutation
% 2.04/0.63  
% 2.04/0.63  % (13597)Memory used [KB]: 7291
% 2.04/0.63  % (13597)Time elapsed: 0.227 s
% 2.04/0.63  % (13597)------------------------------
% 2.04/0.63  % (13597)------------------------------
% 2.04/0.63  % (13575)Success in time 0.275 s
%------------------------------------------------------------------------------
