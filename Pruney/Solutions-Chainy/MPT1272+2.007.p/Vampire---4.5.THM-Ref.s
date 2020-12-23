%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:39 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 257 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :    9
%              Number of atoms          :  412 ( 678 expanded)
%              Number of equality atoms :   41 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1010,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f136,f144,f153,f193,f202,f240,f244,f508,f595,f602,f625,f875,f994])).

fof(f994,plain,
    ( spl2_10
    | ~ spl2_45 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | spl2_10
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f982,f143])).

fof(f143,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_10
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f982,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_45 ),
    inference(resolution,[],[f837,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f837,plain,
    ( ! [X0] : r1_tarski(X0,k4_xboole_0(X0,k1_tops_1(sK0,sK1)))
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f833,f70])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f833,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_tops_1(sK0,sK1)))
    | ~ spl2_45 ),
    inference(resolution,[],[f507,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f507,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl2_45
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f875,plain,
    ( spl2_44
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_49
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f822,f623,f600,f238,f151,f84,f503])).

fof(f503,plain,
    ( spl2_44
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f84,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f151,plain,
    ( spl2_11
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f238,plain,
    ( spl2_16
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f600,plain,
    ( spl2_49
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f623,plain,
    ( spl2_54
  <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f822,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_49
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f821,f152])).

fof(f152,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f821,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_49
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f816,f601])).

fof(f601,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f600])).

fof(f816,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_54 ),
    inference(superposition,[],[f252,f624])).

fof(f624,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f623])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k4_xboole_0(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f250,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k4_xboole_0(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl2_16 ),
    inference(superposition,[],[f50,f239])).

fof(f239,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f625,plain,
    ( spl2_54
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f168,f151,f623])).

fof(f168,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl2_11 ),
    inference(resolution,[],[f152,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f602,plain,
    ( spl2_49
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f596,f593,f200,f151,f84,f76,f600])).

fof(f76,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f200,plain,
    ( spl2_15
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f593,plain,
    ( spl2_48
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f596,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f594,f230])).

fof(f230,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f229,f168])).

fof(f229,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f228,f110])).

fof(f110,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f98,f97])).

fof(f97,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f53])).

fof(f98,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f228,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f214,f77])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl2_15 ),
    inference(resolution,[],[f201,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f201,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f594,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f593])).

fof(f595,plain,
    ( spl2_48
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f224,f200,f76,f593])).

fof(f224,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f210,f77])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_15 ),
    inference(resolution,[],[f201,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f508,plain,
    ( ~ spl2_44
    | spl2_45
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f287,f242,f151,f84,f76,f506,f503])).

fof(f242,plain,
    ( spl2_17
  <=> k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f287,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f285,f243])).

fof(f243,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f242])).

fof(f285,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f104,f152])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) )
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f89,f77])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f244,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f177,f151,f134,f76,f242])).

fof(f134,plain,
    ( spl2_8
  <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f177,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f176,f135])).

fof(f135,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f176,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f163,f77])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_11 ),
    inference(resolution,[],[f152,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f240,plain,
    ( spl2_16
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f97,f84,f238])).

fof(f202,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f194,f191,f84,f200])).

fof(f191,plain,
    ( spl2_13
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f194,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f192,f97])).

fof(f192,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl2_13
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f96,f84,f191])).

fof(f96,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f153,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f108,f84,f76,f151])).

fof(f108,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f93,f77])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f144,plain,
    ( ~ spl2_10
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f107,f84,f76,f142])).

fof(f107,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f106,f101])).

fof(f101,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f46,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(f100,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f87,f77])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f106,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f91,f77])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f136,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f103,f84,f80,f76,f134])).

fof(f80,plain,
    ( spl2_2
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f103,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f102,f81])).

fof(f81,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f102,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f88,f77])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f86,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f47,f76])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:35:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (18789)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (18804)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (18785)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (18796)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (18783)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (18802)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (18782)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (18812)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (18786)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (18788)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (18787)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (18784)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (18810)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (18808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (18801)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (18807)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (18791)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (18811)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (18803)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (18792)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (18793)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (18798)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (18797)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (18794)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (18799)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (18800)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (18795)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (18790)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (18806)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (18809)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.79/0.62  % (18809)Refutation found. Thanks to Tanya!
% 1.79/0.62  % SZS status Theorem for theBenchmark
% 1.79/0.62  % SZS output start Proof for theBenchmark
% 1.79/0.62  fof(f1010,plain,(
% 1.79/0.62    $false),
% 1.79/0.62    inference(avatar_sat_refutation,[],[f78,f82,f86,f136,f144,f153,f193,f202,f240,f244,f508,f595,f602,f625,f875,f994])).
% 1.79/0.62  fof(f994,plain,(
% 1.79/0.62    spl2_10 | ~spl2_45),
% 1.79/0.62    inference(avatar_contradiction_clause,[],[f993])).
% 1.79/0.62  fof(f993,plain,(
% 1.79/0.62    $false | (spl2_10 | ~spl2_45)),
% 1.79/0.62    inference(subsumption_resolution,[],[f982,f143])).
% 1.79/0.62  fof(f143,plain,(
% 1.79/0.62    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_10),
% 1.79/0.62    inference(avatar_component_clause,[],[f142])).
% 1.79/0.62  fof(f142,plain,(
% 1.79/0.62    spl2_10 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.79/0.62  fof(f982,plain,(
% 1.79/0.62    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_45),
% 1.79/0.62    inference(resolution,[],[f837,f69])).
% 1.79/0.62  fof(f69,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 1.79/0.62    inference(cnf_transformation,[],[f40])).
% 1.79/0.62  fof(f40,plain,(
% 1.79/0.62    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f5])).
% 1.79/0.62  fof(f5,axiom,(
% 1.79/0.62    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.79/0.62  fof(f837,plain,(
% 1.79/0.62    ( ! [X0] : (r1_tarski(X0,k4_xboole_0(X0,k1_tops_1(sK0,sK1)))) ) | ~spl2_45),
% 1.79/0.62    inference(forward_demodulation,[],[f833,f70])).
% 1.79/0.62  fof(f70,plain,(
% 1.79/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.79/0.62    inference(cnf_transformation,[],[f6])).
% 1.79/0.62  fof(f6,axiom,(
% 1.79/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.79/0.62  fof(f833,plain,(
% 1.79/0.62    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_tops_1(sK0,sK1)))) ) | ~spl2_45),
% 1.79/0.62    inference(resolution,[],[f507,f64])).
% 1.79/0.62  fof(f64,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f39])).
% 1.79/0.62  fof(f39,plain,(
% 1.79/0.62    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.79/0.62    inference(ennf_transformation,[],[f3])).
% 1.79/0.62  fof(f3,axiom,(
% 1.79/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.79/0.62  fof(f507,plain,(
% 1.79/0.62    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | ~spl2_45),
% 1.79/0.62    inference(avatar_component_clause,[],[f506])).
% 1.79/0.62  fof(f506,plain,(
% 1.79/0.62    spl2_45 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.79/0.62  fof(f875,plain,(
% 1.79/0.62    spl2_44 | ~spl2_3 | ~spl2_11 | ~spl2_16 | ~spl2_49 | ~spl2_54),
% 1.79/0.62    inference(avatar_split_clause,[],[f822,f623,f600,f238,f151,f84,f503])).
% 1.79/0.62  fof(f503,plain,(
% 1.79/0.62    spl2_44 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.79/0.62  fof(f84,plain,(
% 1.79/0.62    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.79/0.62  fof(f151,plain,(
% 1.79/0.62    spl2_11 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.79/0.62  fof(f238,plain,(
% 1.79/0.62    spl2_16 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.79/0.62  fof(f600,plain,(
% 1.79/0.62    spl2_49 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 1.79/0.62  fof(f623,plain,(
% 1.79/0.62    spl2_54 <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.79/0.62  fof(f822,plain,(
% 1.79/0.62    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_11 | ~spl2_16 | ~spl2_49 | ~spl2_54)),
% 1.79/0.62    inference(subsumption_resolution,[],[f821,f152])).
% 1.79/0.62  fof(f152,plain,(
% 1.79/0.62    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 1.79/0.62    inference(avatar_component_clause,[],[f151])).
% 1.79/0.62  fof(f821,plain,(
% 1.79/0.62    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_16 | ~spl2_49 | ~spl2_54)),
% 1.79/0.62    inference(subsumption_resolution,[],[f816,f601])).
% 1.79/0.62  fof(f601,plain,(
% 1.79/0.62    r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_49),
% 1.79/0.62    inference(avatar_component_clause,[],[f600])).
% 1.79/0.62  fof(f816,plain,(
% 1.79/0.62    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_16 | ~spl2_54)),
% 1.79/0.62    inference(superposition,[],[f252,f624])).
% 1.79/0.62  fof(f624,plain,(
% 1.79/0.62    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl2_54),
% 1.79/0.62    inference(avatar_component_clause,[],[f623])).
% 1.79/0.62  fof(f252,plain,(
% 1.79/0.62    ( ! [X0] : (~r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl2_3 | ~spl2_16)),
% 1.79/0.62    inference(subsumption_resolution,[],[f250,f85])).
% 1.79/0.62  fof(f85,plain,(
% 1.79/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.79/0.62    inference(avatar_component_clause,[],[f84])).
% 1.79/0.62  fof(f250,plain,(
% 1.79/0.62    ( ! [X0] : (~r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | ~spl2_16),
% 1.79/0.62    inference(superposition,[],[f50,f239])).
% 1.79/0.62  fof(f239,plain,(
% 1.79/0.62    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_16),
% 1.79/0.62    inference(avatar_component_clause,[],[f238])).
% 1.79/0.62  fof(f50,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f28,plain,(
% 1.79/0.62    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f14])).
% 1.79/0.62  fof(f14,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.79/0.62  fof(f625,plain,(
% 1.79/0.62    spl2_54 | ~spl2_11),
% 1.79/0.62    inference(avatar_split_clause,[],[f168,f151,f623])).
% 1.79/0.62  fof(f168,plain,(
% 1.79/0.62    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl2_11),
% 1.79/0.62    inference(resolution,[],[f152,f53])).
% 1.79/0.62  fof(f53,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f30])).
% 1.79/0.62  fof(f30,plain,(
% 1.79/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f9])).
% 1.79/0.62  fof(f9,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.79/0.62  fof(f602,plain,(
% 1.79/0.62    spl2_49 | ~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_15 | ~spl2_48),
% 1.79/0.62    inference(avatar_split_clause,[],[f596,f593,f200,f151,f84,f76,f600])).
% 1.79/0.62  fof(f76,plain,(
% 1.79/0.62    spl2_1 <=> l1_pre_topc(sK0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.79/0.62  fof(f200,plain,(
% 1.79/0.62    spl2_15 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.79/0.62  fof(f593,plain,(
% 1.79/0.62    spl2_48 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 1.79/0.62  fof(f596,plain,(
% 1.79/0.62    r1_tarski(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_15 | ~spl2_48)),
% 1.79/0.62    inference(forward_demodulation,[],[f594,f230])).
% 1.79/0.62  fof(f230,plain,(
% 1.79/0.62    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_15)),
% 1.79/0.62    inference(forward_demodulation,[],[f229,f168])).
% 1.79/0.62  fof(f229,plain,(
% 1.79/0.62    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_15)),
% 1.79/0.62    inference(forward_demodulation,[],[f228,f110])).
% 1.79/0.62  fof(f110,plain,(
% 1.79/0.62    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 1.79/0.62    inference(forward_demodulation,[],[f98,f97])).
% 1.79/0.62  fof(f97,plain,(
% 1.79/0.62    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f53])).
% 1.79/0.62  fof(f98,plain,(
% 1.79/0.62    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f52])).
% 1.79/0.62  fof(f52,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.79/0.62    inference(cnf_transformation,[],[f29])).
% 1.79/0.62  fof(f29,plain,(
% 1.79/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f12])).
% 1.79/0.62  fof(f12,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.79/0.62  fof(f228,plain,(
% 1.79/0.62    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl2_1 | ~spl2_15)),
% 1.79/0.62    inference(subsumption_resolution,[],[f214,f77])).
% 1.79/0.62  fof(f77,plain,(
% 1.79/0.62    l1_pre_topc(sK0) | ~spl2_1),
% 1.79/0.62    inference(avatar_component_clause,[],[f76])).
% 1.79/0.62  fof(f214,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | ~spl2_15),
% 1.79/0.62    inference(resolution,[],[f201,f72])).
% 1.79/0.62  fof(f72,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f43])).
% 1.79/0.62  fof(f43,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f17])).
% 1.79/0.62  fof(f17,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.79/0.62  fof(f201,plain,(
% 1.79/0.62    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_15),
% 1.79/0.62    inference(avatar_component_clause,[],[f200])).
% 1.79/0.62  fof(f594,plain,(
% 1.79/0.62    r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_48),
% 1.79/0.62    inference(avatar_component_clause,[],[f593])).
% 1.79/0.62  fof(f595,plain,(
% 1.79/0.62    spl2_48 | ~spl2_1 | ~spl2_15),
% 1.79/0.62    inference(avatar_split_clause,[],[f224,f200,f76,f593])).
% 1.79/0.62  fof(f224,plain,(
% 1.79/0.62    r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_15)),
% 1.79/0.62    inference(subsumption_resolution,[],[f210,f77])).
% 1.79/0.62  fof(f210,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_15),
% 1.79/0.62    inference(resolution,[],[f201,f60])).
% 1.79/0.62  fof(f60,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f35])).
% 1.79/0.62  fof(f35,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f20])).
% 1.79/0.62  fof(f20,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.79/0.62  fof(f508,plain,(
% 1.79/0.62    ~spl2_44 | spl2_45 | ~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_17),
% 1.79/0.62    inference(avatar_split_clause,[],[f287,f242,f151,f84,f76,f506,f503])).
% 1.79/0.62  fof(f242,plain,(
% 1.79/0.62    spl2_17 <=> k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.79/0.62  fof(f287,plain,(
% 1.79/0.62    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_11 | ~spl2_17)),
% 1.79/0.62    inference(forward_demodulation,[],[f285,f243])).
% 1.79/0.62  fof(f243,plain,(
% 1.79/0.62    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_17),
% 1.79/0.62    inference(avatar_component_clause,[],[f242])).
% 1.79/0.62  fof(f285,plain,(
% 1.79/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_1 | ~spl2_3 | ~spl2_11)),
% 1.79/0.62    inference(resolution,[],[f104,f152])).
% 1.79/0.62  fof(f104,plain,(
% 1.79/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) ) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f89,f77])).
% 1.79/0.62  fof(f89,plain,(
% 1.79/0.62    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) ) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f59])).
% 1.79/0.62  fof(f59,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f34])).
% 1.79/0.62  fof(f34,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(flattening,[],[f33])).
% 1.79/0.62  fof(f33,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f21])).
% 1.79/0.62  fof(f21,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.79/0.62  fof(f244,plain,(
% 1.79/0.62    spl2_17 | ~spl2_1 | ~spl2_8 | ~spl2_11),
% 1.79/0.62    inference(avatar_split_clause,[],[f177,f151,f134,f76,f242])).
% 1.79/0.62  fof(f134,plain,(
% 1.79/0.62    spl2_8 <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.79/0.62  fof(f177,plain,(
% 1.79/0.62    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_8 | ~spl2_11)),
% 1.79/0.62    inference(subsumption_resolution,[],[f176,f135])).
% 1.79/0.62  fof(f135,plain,(
% 1.79/0.62    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~spl2_8),
% 1.79/0.62    inference(avatar_component_clause,[],[f134])).
% 1.79/0.62  fof(f176,plain,(
% 1.79/0.62    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_11)),
% 1.79/0.62    inference(subsumption_resolution,[],[f163,f77])).
% 1.79/0.62  fof(f163,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~spl2_11),
% 1.79/0.62    inference(resolution,[],[f152,f62])).
% 1.79/0.62  fof(f62,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f36])).
% 1.79/0.62  fof(f36,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f22])).
% 1.79/0.62  fof(f22,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.79/0.62  fof(f240,plain,(
% 1.79/0.62    spl2_16 | ~spl2_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f97,f84,f238])).
% 1.79/0.62  fof(f202,plain,(
% 1.79/0.62    spl2_15 | ~spl2_3 | ~spl2_13),
% 1.79/0.62    inference(avatar_split_clause,[],[f194,f191,f84,f200])).
% 1.79/0.62  fof(f191,plain,(
% 1.79/0.62    spl2_13 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.79/0.62  fof(f194,plain,(
% 1.79/0.62    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_13)),
% 1.79/0.62    inference(forward_demodulation,[],[f192,f97])).
% 1.79/0.62  fof(f192,plain,(
% 1.79/0.62    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_13),
% 1.79/0.62    inference(avatar_component_clause,[],[f191])).
% 1.79/0.62  fof(f193,plain,(
% 1.79/0.62    spl2_13 | ~spl2_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f96,f84,f191])).
% 1.79/0.62  fof(f96,plain,(
% 1.79/0.62    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f54])).
% 1.79/0.62  fof(f54,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f31])).
% 1.79/0.62  fof(f31,plain,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f10])).
% 1.79/0.62  fof(f10,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.79/0.62  fof(f153,plain,(
% 1.79/0.62    spl2_11 | ~spl2_1 | ~spl2_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f108,f84,f76,f151])).
% 1.79/0.62  fof(f108,plain,(
% 1.79/0.62    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f93,f77])).
% 1.79/0.62  fof(f93,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f71])).
% 1.79/0.62  fof(f71,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f42])).
% 1.79/0.62  fof(f42,plain,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(flattening,[],[f41])).
% 1.79/0.62  fof(f41,plain,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f16])).
% 1.79/0.62  fof(f16,axiom,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.79/0.62  fof(f144,plain,(
% 1.79/0.62    ~spl2_10 | ~spl2_1 | ~spl2_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f107,f84,f76,f142])).
% 1.79/0.62  fof(f107,plain,(
% 1.79/0.62    k1_xboole_0 != k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f106,f101])).
% 1.79/0.62  fof(f101,plain,(
% 1.79/0.62    ~v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f100,f46])).
% 1.79/0.62  fof(f46,plain,(
% 1.79/0.62    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  fof(f26,plain,(
% 1.79/0.62    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.79/0.62    inference(flattening,[],[f25])).
% 1.79/0.62  fof(f25,plain,(
% 1.79/0.62    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f24])).
% 1.79/0.62  fof(f24,negated_conjecture,(
% 1.79/0.62    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.62    inference(negated_conjecture,[],[f23])).
% 1.79/0.62  fof(f23,conjecture,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).
% 1.79/0.62  fof(f100,plain,(
% 1.79/0.62    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f87,f77])).
% 1.79/0.62  fof(f87,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f49])).
% 1.79/0.62  fof(f49,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f27])).
% 1.79/0.62  fof(f27,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f18])).
% 1.79/0.62  fof(f18,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 1.79/0.62  fof(f106,plain,(
% 1.79/0.62    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f91,f77])).
% 1.79/0.62  fof(f91,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f61])).
% 1.79/0.62  fof(f61,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f36])).
% 1.79/0.62  fof(f136,plain,(
% 1.79/0.62    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f103,f84,f80,f76,f134])).
% 1.79/0.62  fof(f80,plain,(
% 1.79/0.62    spl2_2 <=> v3_tops_1(sK1,sK0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.79/0.62  fof(f103,plain,(
% 1.79/0.62    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f102,f81])).
% 1.79/0.62  fof(f81,plain,(
% 1.79/0.62    v3_tops_1(sK1,sK0) | ~spl2_2),
% 1.79/0.62    inference(avatar_component_clause,[],[f80])).
% 1.79/0.62  fof(f102,plain,(
% 1.79/0.62    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v3_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.79/0.62    inference(subsumption_resolution,[],[f88,f77])).
% 1.79/0.62  fof(f88,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v3_tops_1(sK1,sK0) | ~spl2_3),
% 1.79/0.62    inference(resolution,[],[f85,f56])).
% 1.79/0.62  fof(f56,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f32])).
% 1.79/0.62  fof(f32,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f19])).
% 1.79/0.62  fof(f19,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).
% 1.79/0.62  fof(f86,plain,(
% 1.79/0.62    spl2_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f44,f84])).
% 1.79/0.62  fof(f44,plain,(
% 1.79/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  fof(f82,plain,(
% 1.79/0.62    spl2_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f45,f80])).
% 1.79/0.62  fof(f45,plain,(
% 1.79/0.62    v3_tops_1(sK1,sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  fof(f78,plain,(
% 1.79/0.62    spl2_1),
% 1.79/0.62    inference(avatar_split_clause,[],[f47,f76])).
% 1.79/0.62  fof(f47,plain,(
% 1.79/0.62    l1_pre_topc(sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  % SZS output end Proof for theBenchmark
% 1.79/0.62  % (18809)------------------------------
% 1.79/0.62  % (18809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (18809)Termination reason: Refutation
% 1.79/0.62  
% 1.79/0.62  % (18809)Memory used [KB]: 6908
% 1.79/0.62  % (18809)Time elapsed: 0.208 s
% 1.79/0.62  % (18809)------------------------------
% 1.79/0.62  % (18809)------------------------------
% 1.79/0.62  % (18781)Success in time 0.258 s
%------------------------------------------------------------------------------
