%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 269 expanded)
%              Number of leaves         :   29 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  504 (1626 expanded)
%              Number of equality atoms :   65 ( 232 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f88,f93,f98,f103,f140,f159,f199,f203,f225,f269,f275,f312])).

fof(f312,plain,
    ( spl3_2
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl3_2
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f310,f126])).

fof(f126,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f55,f116])).

fof(f116,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f49,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f310,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl3_2
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f307,f68])).

fof(f68,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f307,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f274,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f274,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_24
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f275,plain,
    ( spl3_24
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f270,f222,f196,f272])).

fof(f196,plain,
    ( spl3_16
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f222,plain,
    ( spl3_19
  <=> r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f270,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f224,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f224,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f269,plain,
    ( spl3_1
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f268,f196,f95,f90,f62])).

fof(f62,plain,
    ( spl3_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( spl3_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f268,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f267,f97])).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f267,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f261,f92])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f261,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_16 ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_16 ),
    inference(superposition,[],[f51,f198])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f225,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f220,f95,f90,f81,f76,f71,f222])).

fof(f71,plain,
    ( spl3_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( spl3_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f220,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f219,f78])).

fof(f78,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f219,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f214,f73])).

fof(f73,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f214,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f83,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f162,f97])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f92])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f203,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f202,f95,f90,f62,f196])).

fof(f202,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f160,f97])).

fof(f160,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f50,f92])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f199,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f194,f156,f137,f90,f86,f196])).

fof(f86,plain,
    ( spl3_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f137,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f156,plain,
    ( spl3_15
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f194,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f192,f139])).

fof(f139,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f192,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(resolution,[],[f189,f158])).

fof(f158,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f174,f92])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(superposition,[],[f173,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k3_xboole_0(X0,X1),sK0)
        | k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_tarski(k3_xboole_0(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k3_xboole_0(X0,X1),sK0)
        | k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_tarski(k3_xboole_0(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_6 ),
    inference(superposition,[],[f130,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
        | k1_xboole_0 = k9_subset_1(u1_struct_0(sK0),X1,X0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_6 ),
    inference(resolution,[],[f57,f87])).

fof(f87,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f159,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f154,f100,f95,f90,f156])).

fof(f100,plain,
    ( spl3_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f154,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f153,f102])).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f153,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f151,f97])).

fof(f151,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f53,f92])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f140,plain,
    ( spl3_12
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f135,f95,f90,f137])).

fof(f135,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f133,f97])).

fof(f133,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f103,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f100])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f98,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f39,f86,f62])).

fof(f39,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f40,f81,f62])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f41,f76,f62])).

fof(f41,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f42,f71,f62])).

fof(f42,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f66,f62])).

fof(f43,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4228)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (4220)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (4228)Refutation not found, incomplete strategy% (4228)------------------------------
% 0.21/0.51  % (4228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4207)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (4199)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (4228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4228)Memory used [KB]: 1663
% 0.21/0.51  % (4228)Time elapsed: 0.058 s
% 0.21/0.51  % (4228)------------------------------
% 0.21/0.51  % (4228)------------------------------
% 0.21/0.52  % (4201)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (4205)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4214)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (4220)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f88,f93,f98,f103,f140,f159,f199,f203,f225,f269,f275,f312])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    spl3_2 | ~spl3_24),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    $false | (spl3_2 | ~spl3_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f310,f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 0.21/0.52    inference(superposition,[],[f55,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.52    inference(superposition,[],[f49,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,sK2) | (spl3_2 | ~spl3_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f307,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    k1_xboole_0 != sK2 | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl3_24),
% 0.21/0.52    inference(resolution,[],[f274,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_xboole_0) | ~spl3_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f272])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    spl3_24 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    spl3_24 | ~spl3_16 | ~spl3_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f270,f222,f196,f272])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    spl3_16 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    spl3_19 <=> r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_xboole_0) | (~spl3_16 | ~spl3_19)),
% 0.21/0.52    inference(forward_demodulation,[],[f224,f198])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f196])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | ~spl3_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f222])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    spl3_1 | ~spl3_7 | ~spl3_8 | ~spl3_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f268,f196,f95,f90,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl3_1 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl3_8 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    v2_tops_1(sK1,sK0) | (~spl3_7 | ~spl3_8 | ~spl3_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f267,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_7 | ~spl3_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f261,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_16),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f260])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_16),
% 0.21/0.52    inference(superposition,[],[f51,f198])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    spl3_19 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f220,f95,f90,f81,f76,f71,f222])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl3_3 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl3_4 <=> r1_tarski(sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f219,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r1_tarski(sK2,sK1) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK2,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f214,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    v3_pre_topc(sK2,sK0) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ~v3_pre_topc(sK2,sK0) | r1_tarski(sK2,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK2,sK1) | (~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(resolution,[],[f83,f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) ) | (~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f162,f97])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f54,f92])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    spl3_16 | ~spl3_1 | ~spl3_7 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f202,f95,f90,f62,f196])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f97])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f50,f92])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    spl3_16 | ~spl3_6 | ~spl3_7 | ~spl3_12 | ~spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f194,f156,f137,f90,f86,f196])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl3_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl3_15 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_6 | ~spl3_7 | ~spl3_12 | ~spl3_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_6 | ~spl3_7 | ~spl3_15)),
% 0.21/0.52    inference(resolution,[],[f189,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f156])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.52    inference(resolution,[],[f174,f92])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.21/0.52    inference(superposition,[],[f173,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_pre_topc(k3_xboole_0(X0,X1),sK0) | k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_tarski(k3_xboole_0(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_6),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_pre_topc(k3_xboole_0(X0,X1),sK0) | k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_tarski(k3_xboole_0(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_6),
% 0.21/0.52    inference(superposition,[],[f130,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) | k1_xboole_0 = k9_subset_1(u1_struct_0(sK0),X1,X0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_6),
% 0.21/0.52    inference(resolution,[],[f57,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl3_15 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f154,f100,f95,f90,f156])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl3_9 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f151,f97])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f53,f92])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl3_12 | ~spl3_7 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f135,f95,f90,f137])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f133,f97])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f56,f92])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f100])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f95])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f90])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl3_1 | spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f86,f62])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~spl3_1 | spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f81,f62])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~spl3_1 | spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f76,f62])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ~spl3_1 | spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f71,f62])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f66,f62])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (4220)------------------------------
% 0.21/0.52  % (4220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4220)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (4220)Memory used [KB]: 6396
% 0.21/0.52  % (4220)Time elapsed: 0.067 s
% 0.21/0.52  % (4220)------------------------------
% 0.21/0.52  % (4220)------------------------------
% 0.21/0.53  % (4200)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (4198)Success in time 0.164 s
%------------------------------------------------------------------------------
