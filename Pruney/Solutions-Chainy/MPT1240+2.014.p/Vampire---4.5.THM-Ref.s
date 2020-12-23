%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:17 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 274 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  426 ( 894 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f81,f123,f166,f198,f247,f371,f420,f468,f478,f481,f685,f768,f1053,f1095,f1099])).

fof(f1099,plain,
    ( ~ spl4_2
    | spl4_96 ),
    inference(avatar_contradiction_clause,[],[f1096])).

fof(f1096,plain,
    ( $false
    | ~ spl4_2
    | spl4_96 ),
    inference(resolution,[],[f1094,f860])).

fof(f860,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl4_2 ),
    inference(superposition,[],[f48,f762])).

fof(f762,plain,
    ( k1_tarski(sK1) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl4_2 ),
    inference(superposition,[],[f751,f249])).

fof(f249,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k3_subset_1(X3,k4_xboole_0(X3,X4)) ),
    inference(resolution,[],[f90,f48])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f751,plain,
    ( k1_tarski(sK1) = k3_subset_1(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f557,f555])).

fof(f555,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK1)) = k3_subset_1(sK3,k1_tarski(sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f250,f63])).

fof(f63,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f250,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,X5)
      | k4_xboole_0(X5,k1_tarski(X6)) = k3_subset_1(X5,k1_tarski(X6)) ) ),
    inference(resolution,[],[f90,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f557,plain,
    ( k1_tarski(sK1) = k3_subset_1(sK3,k3_subset_1(sK3,k1_tarski(sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f258,f63])).

fof(f258,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,X5)
      | k1_tarski(X6) = k3_subset_1(X5,k3_subset_1(X5,k1_tarski(X6))) ) ),
    inference(resolution,[],[f93,f55])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f50,f53])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1094,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK3)
    | spl4_96 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1093,plain,
    ( spl4_96
  <=> r1_tarski(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1095,plain,
    ( ~ spl4_96
    | ~ spl4_39
    | ~ spl4_3
    | spl4_1
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1080,f1051,f59,f66,f369,f1093])).

fof(f369,plain,
    ( spl4_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f66,plain,
    ( spl4_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_1
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1051,plain,
    ( spl4_94
  <=> ! [X0] :
        ( r1_tarski(sK3,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1080,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK1),sK3)
    | spl4_1
    | ~ spl4_94 ),
    inference(resolution,[],[f1052,f482])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,sK2))
        | ~ r1_tarski(k1_tarski(sK1),X0) )
    | spl4_1 ),
    inference(resolution,[],[f77,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r1_tarski(k1_tarski(X2),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f77,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f1052,plain,
    ( ! [X0] :
        ( r1_tarski(sK3,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1053,plain,
    ( ~ spl4_11
    | ~ spl4_5
    | spl4_94
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1036,f626,f196,f74,f1051,f74,f119])).

fof(f119,plain,
    ( spl4_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f74,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f196,plain,
    ( spl4_20
  <=> k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f626,plain,
    ( spl4_64
  <=> k4_xboole_0(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1036,plain,
    ( ! [X0] :
        ( r1_tarski(sK3,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_64 ),
    inference(superposition,[],[f47,f1021])).

fof(f1021,plain,
    ( sK3 = k1_tops_1(sK0,sK3)
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f1018,f95])).

fof(f95,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f92,f89])).

fof(f89,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK3) = k3_subset_1(u1_struct_0(sK0),sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f49,f75])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f92,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f50,f75])).

fof(f1018,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3)
    | ~ spl4_20
    | ~ spl4_64 ),
    inference(backward_demodulation,[],[f197,f627])).

fof(f627,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f626])).

fof(f197,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f768,plain,
    ( ~ spl4_11
    | ~ spl4_39
    | ~ spl4_55
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f764,f466,f473,f369,f119])).

fof(f473,plain,
    ( spl4_55
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f466,plain,
    ( spl4_53
  <=> ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f764,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_53 ),
    inference(resolution,[],[f467,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f467,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f466])).

fof(f685,plain,
    ( ~ spl4_11
    | spl4_64
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f682,f164,f626,f119])).

fof(f164,plain,
    ( spl4_18
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f682,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f272,f165])).

fof(f165,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f272,plain,(
    ! [X4,X3] :
      ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X3),X4),X3)
      | k4_xboole_0(u1_struct_0(X3),X4) = k2_pre_topc(X3,k4_xboole_0(u1_struct_0(X3),X4))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,u1_struct_0(X2))
      | ~ v4_pre_topc(X3,X2)
      | k2_pre_topc(X2,X3) = X3
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f44,f53])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f481,plain,
    ( ~ spl4_11
    | ~ spl4_39
    | spl4_49 ),
    inference(avatar_split_clause,[],[f479,f426,f369,f119])).

fof(f426,plain,
    ( spl4_49
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f479,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_49 ),
    inference(resolution,[],[f427,f41])).

fof(f427,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl4_49 ),
    inference(avatar_component_clause,[],[f426])).

fof(f478,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | spl4_55 ),
    inference(resolution,[],[f474,f82])).

fof(f82,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f474,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f473])).

fof(f468,plain,
    ( ~ spl4_49
    | ~ spl4_1
    | spl4_53
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f443,f354,f79,f466,f59,f426])).

fof(f79,plain,
    ( spl4_6
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f354,plain,
    ( spl4_36
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f443,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
        | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) )
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(resolution,[],[f199,f364])).

fof(f364,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f354])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ r2_hidden(sK1,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f179,f57])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X1,sK2)
        | ~ v3_pre_topc(X1,sK0)
        | ~ r2_hidden(sK1,X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f420,plain,(
    spl4_39 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl4_39 ),
    inference(resolution,[],[f370,f38])).

fof(f370,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f369])).

fof(f371,plain,
    ( ~ spl4_27
    | ~ spl4_39
    | ~ spl4_11
    | spl4_36 ),
    inference(avatar_split_clause,[],[f367,f354,f119,f369,f240])).

fof(f240,plain,
    ( spl4_27
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f367,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl4_36 ),
    inference(resolution,[],[f355,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f355,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f354])).

fof(f247,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl4_27 ),
    inference(resolution,[],[f241,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f241,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f198,plain,
    ( ~ spl4_11
    | spl4_20
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f194,f74,f196,f119])).

fof(f194,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f188,f89])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl4_5 ),
    inference(resolution,[],[f42,f75])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f166,plain,
    ( ~ spl4_4
    | ~ spl4_11
    | ~ spl4_5
    | spl4_18
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f153,f74,f164,f74,f119,f70])).

fof(f70,plain,
    ( spl4_4
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f153,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl4_5 ),
    inference(superposition,[],[f46,f89])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f123,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f120,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f81,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f33,f79,f59])).

fof(f33,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f34,f74,f59])).

fof(f34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f35,f70,f59])).

fof(f35,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f36,f66,f59])).

fof(f36,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f37,f62,f59])).

fof(f37,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:02:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (17525)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (17540)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % (17524)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.54  % (17541)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.44/0.56  % (17523)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.44/0.56  % (17522)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.61/0.57  % (17520)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.61/0.57  % (17528)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.61/0.58  % (17529)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.61/0.59  % (17538)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.61/0.59  % (17532)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.61/0.60  % (17521)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.61/0.60  % (17527)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.61/0.60  % (17526)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.61/0.60  % (17530)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.61/0.61  % (17536)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.61/0.62  % (17537)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.61/0.62  % (17542)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.61/0.63  % (17539)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.61/0.63  % (17543)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.61/0.64  % (17535)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 2.22/0.65  % (17533)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 2.22/0.65  % (17531)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 2.22/0.65  % (17534)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 2.22/0.68  % (17532)Refutation found. Thanks to Tanya!
% 2.22/0.68  % SZS status Theorem for theBenchmark
% 2.22/0.68  % SZS output start Proof for theBenchmark
% 2.22/0.68  fof(f1100,plain,(
% 2.22/0.68    $false),
% 2.22/0.68    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f81,f123,f166,f198,f247,f371,f420,f468,f478,f481,f685,f768,f1053,f1095,f1099])).
% 2.22/0.68  fof(f1099,plain,(
% 2.22/0.68    ~spl4_2 | spl4_96),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f1096])).
% 2.22/0.68  fof(f1096,plain,(
% 2.22/0.68    $false | (~spl4_2 | spl4_96)),
% 2.22/0.68    inference(resolution,[],[f1094,f860])).
% 2.22/0.68  fof(f860,plain,(
% 2.22/0.68    r1_tarski(k1_tarski(sK1),sK3) | ~spl4_2),
% 2.22/0.68    inference(superposition,[],[f48,f762])).
% 2.22/0.68  fof(f762,plain,(
% 2.22/0.68    k1_tarski(sK1) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1))) | ~spl4_2),
% 2.22/0.68    inference(superposition,[],[f751,f249])).
% 2.22/0.68  fof(f249,plain,(
% 2.22/0.68    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k3_subset_1(X3,k4_xboole_0(X3,X4))) )),
% 2.22/0.68    inference(resolution,[],[f90,f48])).
% 2.22/0.68  fof(f90,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.22/0.68    inference(resolution,[],[f49,f53])).
% 2.22/0.68  fof(f53,plain,(
% 2.22/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f6])).
% 2.22/0.68  fof(f6,axiom,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.22/0.68  fof(f49,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f25])).
% 2.22/0.68  fof(f25,plain,(
% 2.22/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f4])).
% 2.22/0.68  fof(f4,axiom,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.22/0.68  fof(f751,plain,(
% 2.22/0.68    k1_tarski(sK1) = k3_subset_1(sK3,k4_xboole_0(sK3,k1_tarski(sK1))) | ~spl4_2),
% 2.22/0.68    inference(forward_demodulation,[],[f557,f555])).
% 2.22/0.68  fof(f555,plain,(
% 2.22/0.68    k4_xboole_0(sK3,k1_tarski(sK1)) = k3_subset_1(sK3,k1_tarski(sK1)) | ~spl4_2),
% 2.22/0.68    inference(resolution,[],[f250,f63])).
% 2.22/0.68  fof(f63,plain,(
% 2.22/0.68    r2_hidden(sK1,sK3) | ~spl4_2),
% 2.22/0.68    inference(avatar_component_clause,[],[f62])).
% 2.22/0.68  fof(f62,plain,(
% 2.22/0.68    spl4_2 <=> r2_hidden(sK1,sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.68  fof(f250,plain,(
% 2.22/0.68    ( ! [X6,X5] : (~r2_hidden(X6,X5) | k4_xboole_0(X5,k1_tarski(X6)) = k3_subset_1(X5,k1_tarski(X6))) )),
% 2.22/0.68    inference(resolution,[],[f90,f55])).
% 2.22/0.68  fof(f55,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f3])).
% 2.22/0.68  fof(f3,axiom,(
% 2.22/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.22/0.68  fof(f557,plain,(
% 2.22/0.68    k1_tarski(sK1) = k3_subset_1(sK3,k3_subset_1(sK3,k1_tarski(sK1))) | ~spl4_2),
% 2.22/0.68    inference(resolution,[],[f258,f63])).
% 2.22/0.68  fof(f258,plain,(
% 2.22/0.68    ( ! [X6,X5] : (~r2_hidden(X6,X5) | k1_tarski(X6) = k3_subset_1(X5,k3_subset_1(X5,k1_tarski(X6)))) )),
% 2.22/0.68    inference(resolution,[],[f93,f55])).
% 2.22/0.68  fof(f93,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.22/0.68    inference(resolution,[],[f50,f53])).
% 2.22/0.68  fof(f50,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.22/0.68    inference(cnf_transformation,[],[f26])).
% 2.22/0.68  fof(f26,plain,(
% 2.22/0.68    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f5])).
% 2.22/0.68  fof(f5,axiom,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.22/0.68  fof(f48,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f2])).
% 2.22/0.68  fof(f2,axiom,(
% 2.22/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.22/0.68  fof(f1094,plain,(
% 2.22/0.68    ~r1_tarski(k1_tarski(sK1),sK3) | spl4_96),
% 2.22/0.68    inference(avatar_component_clause,[],[f1093])).
% 2.22/0.68  fof(f1093,plain,(
% 2.22/0.68    spl4_96 <=> r1_tarski(k1_tarski(sK1),sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 2.22/0.68  fof(f1095,plain,(
% 2.22/0.68    ~spl4_96 | ~spl4_39 | ~spl4_3 | spl4_1 | ~spl4_94),
% 2.22/0.68    inference(avatar_split_clause,[],[f1080,f1051,f59,f66,f369,f1093])).
% 2.22/0.68  fof(f369,plain,(
% 2.22/0.68    spl4_39 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.22/0.68  fof(f66,plain,(
% 2.22/0.68    spl4_3 <=> r1_tarski(sK3,sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.68  fof(f59,plain,(
% 2.22/0.68    spl4_1 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.68  fof(f1051,plain,(
% 2.22/0.68    spl4_94 <=> ! [X0] : (r1_tarski(sK3,k1_tops_1(sK0,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 2.22/0.68  fof(f1080,plain,(
% 2.22/0.68    ~r1_tarski(sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK1),sK3) | (spl4_1 | ~spl4_94)),
% 2.22/0.68    inference(resolution,[],[f1052,f482])).
% 2.22/0.68  fof(f482,plain,(
% 2.22/0.68    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tarski(sK1),X0)) ) | spl4_1),
% 2.22/0.68    inference(resolution,[],[f77,f86])).
% 2.22/0.68  fof(f86,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r1_tarski(k1_tarski(X2),X0) | ~r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(resolution,[],[f57,f56])).
% 2.22/0.68  fof(f56,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f3])).
% 2.22/0.68  fof(f57,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f32])).
% 2.22/0.68  fof(f32,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.22/0.68    inference(flattening,[],[f31])).
% 2.22/0.68  fof(f31,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.22/0.68    inference(ennf_transformation,[],[f1])).
% 2.22/0.68  fof(f1,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.22/0.68  fof(f77,plain,(
% 2.22/0.68    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl4_1),
% 2.22/0.68    inference(avatar_component_clause,[],[f59])).
% 2.22/0.68  fof(f1052,plain,(
% 2.22/0.68    ( ! [X0] : (r1_tarski(sK3,k1_tops_1(sK0,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_94),
% 2.22/0.68    inference(avatar_component_clause,[],[f1051])).
% 2.22/0.68  fof(f1053,plain,(
% 2.22/0.68    ~spl4_11 | ~spl4_5 | spl4_94 | ~spl4_5 | ~spl4_20 | ~spl4_64),
% 2.22/0.68    inference(avatar_split_clause,[],[f1036,f626,f196,f74,f1051,f74,f119])).
% 2.22/0.68  fof(f119,plain,(
% 2.22/0.68    spl4_11 <=> l1_pre_topc(sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.22/0.68  fof(f74,plain,(
% 2.22/0.68    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.22/0.68  fof(f196,plain,(
% 2.22/0.68    spl4_20 <=> k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.22/0.68  fof(f626,plain,(
% 2.22/0.68    spl4_64 <=> k4_xboole_0(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 2.22/0.68  fof(f1036,plain,(
% 2.22/0.68    ( ! [X0] : (r1_tarski(sK3,k1_tops_1(sK0,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X0) | ~l1_pre_topc(sK0)) ) | (~spl4_5 | ~spl4_20 | ~spl4_64)),
% 2.22/0.68    inference(superposition,[],[f47,f1021])).
% 2.22/0.68  fof(f1021,plain,(
% 2.22/0.68    sK3 = k1_tops_1(sK0,sK3) | (~spl4_5 | ~spl4_20 | ~spl4_64)),
% 2.22/0.68    inference(forward_demodulation,[],[f1018,f95])).
% 2.22/0.68  fof(f95,plain,(
% 2.22/0.68    sK3 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) | ~spl4_5),
% 2.22/0.68    inference(forward_demodulation,[],[f92,f89])).
% 2.22/0.68  fof(f89,plain,(
% 2.22/0.68    k4_xboole_0(u1_struct_0(sK0),sK3) = k3_subset_1(u1_struct_0(sK0),sK3) | ~spl4_5),
% 2.22/0.68    inference(resolution,[],[f49,f75])).
% 2.22/0.68  fof(f75,plain,(
% 2.22/0.68    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 2.22/0.68    inference(avatar_component_clause,[],[f74])).
% 2.22/0.68  fof(f92,plain,(
% 2.22/0.68    sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | ~spl4_5),
% 2.22/0.68    inference(resolution,[],[f50,f75])).
% 2.22/0.68  fof(f1018,plain,(
% 2.22/0.68    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) | (~spl4_20 | ~spl4_64)),
% 2.22/0.68    inference(backward_demodulation,[],[f197,f627])).
% 2.22/0.68  fof(f627,plain,(
% 2.22/0.68    k4_xboole_0(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) | ~spl4_64),
% 2.22/0.68    inference(avatar_component_clause,[],[f626])).
% 2.22/0.68  fof(f197,plain,(
% 2.22/0.68    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) | ~spl4_20),
% 2.22/0.68    inference(avatar_component_clause,[],[f196])).
% 2.22/0.68  fof(f47,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f24])).
% 2.22/0.68  fof(f24,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(flattening,[],[f23])).
% 2.22/0.68  fof(f23,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f13])).
% 2.22/0.68  fof(f13,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.22/0.68  fof(f768,plain,(
% 2.22/0.68    ~spl4_11 | ~spl4_39 | ~spl4_55 | ~spl4_53),
% 2.22/0.68    inference(avatar_split_clause,[],[f764,f466,f473,f369,f119])).
% 2.22/0.68  fof(f473,plain,(
% 2.22/0.68    spl4_55 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 2.22/0.68  fof(f466,plain,(
% 2.22/0.68    spl4_53 <=> ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(k1_tops_1(sK0,sK2),X1))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.22/0.68  fof(f764,plain,(
% 2.22/0.68    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_53),
% 2.22/0.68    inference(resolution,[],[f467,f41])).
% 2.22/0.68  fof(f41,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f18])).
% 2.22/0.68  fof(f18,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f12])).
% 2.22/0.68  fof(f12,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.22/0.68  fof(f467,plain,(
% 2.22/0.68    ( ! [X1] : (~r1_tarski(k1_tops_1(sK0,sK2),X1) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl4_53),
% 2.22/0.68    inference(avatar_component_clause,[],[f466])).
% 2.22/0.68  fof(f685,plain,(
% 2.22/0.68    ~spl4_11 | spl4_64 | ~spl4_18),
% 2.22/0.68    inference(avatar_split_clause,[],[f682,f164,f626,f119])).
% 2.22/0.68  fof(f164,plain,(
% 2.22/0.68    spl4_18 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.22/0.68  fof(f682,plain,(
% 2.22/0.68    k4_xboole_0(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)) | ~l1_pre_topc(sK0) | ~spl4_18),
% 2.22/0.68    inference(resolution,[],[f272,f165])).
% 2.22/0.68  fof(f165,plain,(
% 2.22/0.68    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0) | ~spl4_18),
% 2.22/0.68    inference(avatar_component_clause,[],[f164])).
% 2.22/0.68  fof(f272,plain,(
% 2.22/0.68    ( ! [X4,X3] : (~v4_pre_topc(k4_xboole_0(u1_struct_0(X3),X4),X3) | k4_xboole_0(u1_struct_0(X3),X4) = k2_pre_topc(X3,k4_xboole_0(u1_struct_0(X3),X4)) | ~l1_pre_topc(X3)) )),
% 2.22/0.68    inference(resolution,[],[f102,f48])).
% 2.22/0.68  fof(f102,plain,(
% 2.22/0.68    ( ! [X2,X3] : (~r1_tarski(X3,u1_struct_0(X2)) | ~v4_pre_topc(X3,X2) | k2_pre_topc(X2,X3) = X3 | ~l1_pre_topc(X2)) )),
% 2.22/0.68    inference(resolution,[],[f44,f53])).
% 2.22/0.68  fof(f44,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.22/0.68    inference(cnf_transformation,[],[f21])).
% 2.22/0.68  fof(f21,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(flattening,[],[f20])).
% 2.22/0.68  fof(f20,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f7])).
% 2.22/0.68  fof(f7,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.22/0.68  fof(f481,plain,(
% 2.22/0.68    ~spl4_11 | ~spl4_39 | spl4_49),
% 2.22/0.68    inference(avatar_split_clause,[],[f479,f426,f369,f119])).
% 2.22/0.68  fof(f426,plain,(
% 2.22/0.68    spl4_49 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.22/0.68  fof(f479,plain,(
% 2.22/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_49),
% 2.22/0.68    inference(resolution,[],[f427,f41])).
% 2.22/0.68  fof(f427,plain,(
% 2.22/0.68    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl4_49),
% 2.22/0.68    inference(avatar_component_clause,[],[f426])).
% 2.22/0.68  fof(f478,plain,(
% 2.22/0.68    spl4_55),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f476])).
% 2.22/0.68  fof(f476,plain,(
% 2.22/0.68    $false | spl4_55),
% 2.22/0.68    inference(resolution,[],[f474,f82])).
% 2.22/0.68  fof(f82,plain,(
% 2.22/0.68    r1_tarski(sK2,u1_struct_0(sK0))),
% 2.22/0.68    inference(resolution,[],[f54,f38])).
% 2.22/0.68  fof(f38,plain,(
% 2.22/0.68    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f17,plain,(
% 2.22/0.68    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.22/0.68    inference(flattening,[],[f16])).
% 2.22/0.68  fof(f16,plain,(
% 2.22/0.68    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f15])).
% 2.22/0.68  fof(f15,negated_conjecture,(
% 2.22/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.22/0.68    inference(negated_conjecture,[],[f14])).
% 2.22/0.68  fof(f14,conjecture,(
% 2.22/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 2.22/0.68  fof(f54,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f6])).
% 2.22/0.68  fof(f474,plain,(
% 2.22/0.68    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_55),
% 2.22/0.68    inference(avatar_component_clause,[],[f473])).
% 2.22/0.68  fof(f468,plain,(
% 2.22/0.68    ~spl4_49 | ~spl4_1 | spl4_53 | ~spl4_6 | ~spl4_36),
% 2.22/0.68    inference(avatar_split_clause,[],[f443,f354,f79,f466,f59,f426])).
% 2.22/0.68  fof(f79,plain,(
% 2.22/0.68    spl4_6 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.22/0.68  fof(f354,plain,(
% 2.22/0.68    spl4_36 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.22/0.68  fof(f443,plain,(
% 2.22/0.68    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(k1_tops_1(sK0,sK2),X1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2)) ) | (~spl4_6 | ~spl4_36)),
% 2.22/0.68    inference(resolution,[],[f199,f364])).
% 2.22/0.68  fof(f364,plain,(
% 2.22/0.68    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~spl4_36),
% 2.22/0.68    inference(avatar_component_clause,[],[f354])).
% 2.22/0.68  fof(f199,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK2)) ) | ~spl4_6),
% 2.22/0.68    inference(resolution,[],[f179,f57])).
% 2.22/0.68  fof(f179,plain,(
% 2.22/0.68    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X1,sK2) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(sK1,X1)) ) | ~spl4_6),
% 2.22/0.68    inference(resolution,[],[f80,f53])).
% 2.22/0.68  fof(f80,plain,(
% 2.22/0.68    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0)) ) | ~spl4_6),
% 2.22/0.68    inference(avatar_component_clause,[],[f79])).
% 2.22/0.68  fof(f420,plain,(
% 2.22/0.68    spl4_39),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f418])).
% 2.22/0.68  fof(f418,plain,(
% 2.22/0.68    $false | spl4_39),
% 2.22/0.68    inference(resolution,[],[f370,f38])).
% 2.22/0.68  fof(f370,plain,(
% 2.22/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_39),
% 2.22/0.68    inference(avatar_component_clause,[],[f369])).
% 2.22/0.68  fof(f371,plain,(
% 2.22/0.68    ~spl4_27 | ~spl4_39 | ~spl4_11 | spl4_36),
% 2.22/0.68    inference(avatar_split_clause,[],[f367,f354,f119,f369,f240])).
% 2.22/0.68  fof(f240,plain,(
% 2.22/0.68    spl4_27 <=> v2_pre_topc(sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.22/0.68  fof(f367,plain,(
% 2.22/0.68    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | spl4_36),
% 2.22/0.68    inference(resolution,[],[f355,f51])).
% 2.22/0.68  fof(f51,plain,(
% 2.22/0.68    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f28])).
% 2.22/0.68  fof(f28,plain,(
% 2.22/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.22/0.68    inference(flattening,[],[f27])).
% 2.22/0.68  fof(f27,plain,(
% 2.22/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f10])).
% 2.22/0.68  fof(f10,axiom,(
% 2.22/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.22/0.68  fof(f355,plain,(
% 2.22/0.68    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | spl4_36),
% 2.22/0.68    inference(avatar_component_clause,[],[f354])).
% 2.22/0.68  fof(f247,plain,(
% 2.22/0.68    spl4_27),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f246])).
% 2.22/0.68  fof(f246,plain,(
% 2.22/0.68    $false | spl4_27),
% 2.22/0.68    inference(resolution,[],[f241,f39])).
% 2.22/0.68  fof(f39,plain,(
% 2.22/0.68    v2_pre_topc(sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f241,plain,(
% 2.22/0.68    ~v2_pre_topc(sK0) | spl4_27),
% 2.22/0.68    inference(avatar_component_clause,[],[f240])).
% 2.22/0.68  fof(f198,plain,(
% 2.22/0.68    ~spl4_11 | spl4_20 | ~spl4_5),
% 2.22/0.68    inference(avatar_split_clause,[],[f194,f74,f196,f119])).
% 2.22/0.68  fof(f194,plain,(
% 2.22/0.68    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) | ~l1_pre_topc(sK0) | ~spl4_5),
% 2.22/0.68    inference(forward_demodulation,[],[f188,f89])).
% 2.22/0.68  fof(f188,plain,(
% 2.22/0.68    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | ~spl4_5),
% 2.22/0.68    inference(resolution,[],[f42,f75])).
% 2.22/0.68  fof(f42,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f19])).
% 2.22/0.68  fof(f19,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f8])).
% 2.22/0.68  fof(f8,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.22/0.68  fof(f166,plain,(
% 2.22/0.68    ~spl4_4 | ~spl4_11 | ~spl4_5 | spl4_18 | ~spl4_5),
% 2.22/0.68    inference(avatar_split_clause,[],[f153,f74,f164,f74,f119,f70])).
% 2.22/0.68  fof(f70,plain,(
% 2.22/0.68    spl4_4 <=> v3_pre_topc(sK3,sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.68  fof(f153,plain,(
% 2.22/0.68    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK3,sK0) | ~spl4_5),
% 2.22/0.68    inference(superposition,[],[f46,f89])).
% 2.22/0.68  fof(f46,plain,(
% 2.22/0.68    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f22])).
% 2.22/0.68  fof(f22,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f11])).
% 2.22/0.68  fof(f11,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 2.22/0.68  fof(f123,plain,(
% 2.22/0.68    spl4_11),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f122])).
% 2.22/0.68  fof(f122,plain,(
% 2.22/0.68    $false | spl4_11),
% 2.22/0.68    inference(resolution,[],[f120,f40])).
% 2.22/0.68  fof(f40,plain,(
% 2.22/0.68    l1_pre_topc(sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f120,plain,(
% 2.22/0.68    ~l1_pre_topc(sK0) | spl4_11),
% 2.22/0.68    inference(avatar_component_clause,[],[f119])).
% 2.22/0.68  fof(f81,plain,(
% 2.22/0.68    ~spl4_1 | spl4_6),
% 2.22/0.68    inference(avatar_split_clause,[],[f33,f79,f59])).
% 2.22/0.68  fof(f33,plain,(
% 2.22/0.68    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f76,plain,(
% 2.22/0.68    spl4_1 | spl4_5),
% 2.22/0.68    inference(avatar_split_clause,[],[f34,f74,f59])).
% 2.22/0.68  fof(f34,plain,(
% 2.22/0.68    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f72,plain,(
% 2.22/0.68    spl4_1 | spl4_4),
% 2.22/0.68    inference(avatar_split_clause,[],[f35,f70,f59])).
% 2.22/0.68  fof(f35,plain,(
% 2.22/0.68    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f68,plain,(
% 2.22/0.68    spl4_1 | spl4_3),
% 2.22/0.68    inference(avatar_split_clause,[],[f36,f66,f59])).
% 2.22/0.68  fof(f36,plain,(
% 2.22/0.68    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  fof(f64,plain,(
% 2.22/0.68    spl4_1 | spl4_2),
% 2.22/0.68    inference(avatar_split_clause,[],[f37,f62,f59])).
% 2.22/0.68  fof(f37,plain,(
% 2.22/0.68    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.22/0.68    inference(cnf_transformation,[],[f17])).
% 2.22/0.68  % SZS output end Proof for theBenchmark
% 2.22/0.68  % (17532)------------------------------
% 2.22/0.68  % (17532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (17532)Termination reason: Refutation
% 2.22/0.68  
% 2.22/0.68  % (17532)Memory used [KB]: 11385
% 2.22/0.68  % (17532)Time elapsed: 0.234 s
% 2.22/0.68  % (17532)------------------------------
% 2.22/0.68  % (17532)------------------------------
% 2.47/0.68  % (17519)Success in time 0.315 s
%------------------------------------------------------------------------------
