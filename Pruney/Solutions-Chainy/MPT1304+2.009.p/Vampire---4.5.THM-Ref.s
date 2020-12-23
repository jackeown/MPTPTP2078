%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 147 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  261 ( 536 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f58,f62,f66,f70,f74,f82,f104,f164,f220,f246])).

fof(f246,plain,
    ( ~ spl3_7
    | ~ spl3_10
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_10
    | spl3_33 ),
    inference(subsumption_resolution,[],[f244,f61])).

fof(f61,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f244,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10
    | spl3_33 ),
    inference(resolution,[],[f206,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f206,plain,
    ( ~ m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_33
  <=> m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f220,plain,
    ( ~ spl3_33
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f219,f161,f56,f51,f46,f36,f31,f204])).

fof(f31,plain,
    ( spl3_1
  <=> v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,
    ( spl3_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
        | ~ v1_tops_2(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f161,plain,
    ( spl3_26
  <=> k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f219,plain,
    ( ~ m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f218,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f218,plain,
    ( ~ m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f217,f48])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f217,plain,
    ( ~ m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f216,f38])).

fof(f38,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f216,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f197,f33])).

fof(f33,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f197,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(superposition,[],[f57,f163])).

fof(f163,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f161])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
        | ~ v1_tops_2(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f164,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f153,f102,f46,f161])).

fof(f102,plain,
    ( spl3_15
  <=> ! [X0] :
        ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f153,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(resolution,[],[f103,f48])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f100,f79,f68,f41,f102])).

fof(f41,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f79,plain,
    ( spl3_11
  <=> k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f100,plain,
    ( ! [X0] :
        ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f97,f81])).

fof(f81,plain,
    ( k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f97,plain,
    ( ! [X0] :
        ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f82,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f75,f64,f41,f79])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f66,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f62,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              | ~ v1_tops_2(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              | ~ v1_tops_2(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tops_2)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f31])).

fof(f24,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (23961)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.19/0.40  % (23958)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.40  % (23959)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.40  % (23960)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.40  % (23961)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f247,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f58,f62,f66,f70,f74,f82,f104,f164,f220,f246])).
% 0.19/0.40  fof(f246,plain,(
% 0.19/0.40    ~spl3_7 | ~spl3_10 | spl3_33),
% 0.19/0.40    inference(avatar_contradiction_clause,[],[f245])).
% 0.19/0.40  fof(f245,plain,(
% 0.19/0.40    $false | (~spl3_7 | ~spl3_10 | spl3_33)),
% 0.19/0.40    inference(subsumption_resolution,[],[f244,f61])).
% 0.19/0.40  fof(f61,plain,(
% 0.19/0.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.19/0.40    inference(avatar_component_clause,[],[f60])).
% 0.19/0.40  fof(f60,plain,(
% 0.19/0.40    spl3_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.40  fof(f244,plain,(
% 0.19/0.40    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_10 | spl3_33)),
% 0.19/0.40    inference(resolution,[],[f206,f73])).
% 0.19/0.40  fof(f73,plain,(
% 0.19/0.40    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.19/0.40    inference(avatar_component_clause,[],[f72])).
% 0.19/0.40  fof(f72,plain,(
% 0.19/0.40    spl3_10 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.40  fof(f206,plain,(
% 0.19/0.40    ~m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_33),
% 0.19/0.40    inference(avatar_component_clause,[],[f204])).
% 0.19/0.40  fof(f204,plain,(
% 0.19/0.40    spl3_33 <=> m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.19/0.40  fof(f220,plain,(
% 0.19/0.40    ~spl3_33 | spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_26),
% 0.19/0.40    inference(avatar_split_clause,[],[f219,f161,f56,f51,f46,f36,f31,f204])).
% 0.19/0.40  fof(f31,plain,(
% 0.19/0.40    spl3_1 <=> v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.40  fof(f36,plain,(
% 0.19/0.40    spl3_2 <=> v1_tops_2(sK1,sK0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.40  fof(f46,plain,(
% 0.19/0.40    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.40  fof(f51,plain,(
% 0.19/0.40    spl3_5 <=> l1_pre_topc(sK0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.40  fof(f56,plain,(
% 0.19/0.40    spl3_6 <=> ! [X1,X0,X2] : (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.40  fof(f161,plain,(
% 0.19/0.40    spl3_26 <=> k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.19/0.40  fof(f219,plain,(
% 0.19/0.40    ~m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_26)),
% 0.19/0.40    inference(subsumption_resolution,[],[f218,f53])).
% 0.19/0.40  fof(f53,plain,(
% 0.19/0.40    l1_pre_topc(sK0) | ~spl3_5),
% 0.19/0.40    inference(avatar_component_clause,[],[f51])).
% 0.19/0.40  fof(f218,plain,(
% 0.19/0.40    ~m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_26)),
% 0.19/0.40    inference(subsumption_resolution,[],[f217,f48])).
% 0.19/0.40  fof(f48,plain,(
% 0.19/0.40    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.19/0.40    inference(avatar_component_clause,[],[f46])).
% 0.19/0.40  fof(f217,plain,(
% 0.19/0.40    ~m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_26)),
% 0.19/0.40    inference(subsumption_resolution,[],[f216,f38])).
% 0.19/0.40  fof(f38,plain,(
% 0.19/0.40    v1_tops_2(sK1,sK0) | ~spl3_2),
% 0.19/0.40    inference(avatar_component_clause,[],[f36])).
% 0.19/0.40  fof(f216,plain,(
% 0.19/0.40    ~v1_tops_2(sK1,sK0) | ~m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (spl3_1 | ~spl3_6 | ~spl3_26)),
% 0.19/0.40    inference(subsumption_resolution,[],[f197,f33])).
% 0.19/0.40  fof(f33,plain,(
% 0.19/0.40    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_1),
% 0.19/0.40    inference(avatar_component_clause,[],[f31])).
% 0.19/0.40  fof(f197,plain,(
% 0.19/0.40    v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | ~v1_tops_2(sK1,sK0) | ~m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (~spl3_6 | ~spl3_26)),
% 0.19/0.40    inference(superposition,[],[f57,f163])).
% 0.19/0.40  fof(f163,plain,(
% 0.19/0.40    k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~spl3_26),
% 0.19/0.40    inference(avatar_component_clause,[],[f161])).
% 0.19/0.40  fof(f57,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_6),
% 0.19/0.40    inference(avatar_component_clause,[],[f56])).
% 0.19/0.40  fof(f164,plain,(
% 0.19/0.40    spl3_26 | ~spl3_4 | ~spl3_15),
% 0.19/0.40    inference(avatar_split_clause,[],[f153,f102,f46,f161])).
% 0.19/0.40  fof(f102,plain,(
% 0.19/0.40    spl3_15 <=> ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.40  fof(f153,plain,(
% 0.19/0.40    k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | (~spl3_4 | ~spl3_15)),
% 0.19/0.40    inference(resolution,[],[f103,f48])).
% 0.19/0.40  fof(f103,plain,(
% 0.19/0.40    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) ) | ~spl3_15),
% 0.19/0.40    inference(avatar_component_clause,[],[f102])).
% 0.19/0.40  fof(f104,plain,(
% 0.19/0.40    spl3_15 | ~spl3_3 | ~spl3_9 | ~spl3_11),
% 0.19/0.40    inference(avatar_split_clause,[],[f100,f79,f68,f41,f102])).
% 0.19/0.40  fof(f41,plain,(
% 0.19/0.40    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.40  fof(f68,plain,(
% 0.19/0.40    spl3_9 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.40  fof(f79,plain,(
% 0.19/0.40    spl3_11 <=> k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.40  fof(f100,plain,(
% 0.19/0.40    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_3 | ~spl3_9 | ~spl3_11)),
% 0.19/0.40    inference(forward_demodulation,[],[f97,f81])).
% 0.19/0.40  fof(f81,plain,(
% 0.19/0.40    k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) | ~spl3_11),
% 0.19/0.40    inference(avatar_component_clause,[],[f79])).
% 0.19/0.40  fof(f97,plain,(
% 0.19/0.40    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_3 | ~spl3_9)),
% 0.19/0.40    inference(resolution,[],[f69,f43])).
% 0.19/0.40  fof(f43,plain,(
% 0.19/0.40    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.19/0.40    inference(avatar_component_clause,[],[f41])).
% 0.19/0.40  fof(f69,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.19/0.40    inference(avatar_component_clause,[],[f68])).
% 0.19/0.40  fof(f82,plain,(
% 0.19/0.40    spl3_11 | ~spl3_3 | ~spl3_8),
% 0.19/0.40    inference(avatar_split_clause,[],[f75,f64,f41,f79])).
% 0.19/0.40  fof(f64,plain,(
% 0.19/0.40    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.40  fof(f75,plain,(
% 0.19/0.40    k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) | (~spl3_3 | ~spl3_8)),
% 0.19/0.40    inference(resolution,[],[f65,f43])).
% 0.19/0.40  fof(f65,plain,(
% 0.19/0.40    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_8),
% 0.19/0.40    inference(avatar_component_clause,[],[f64])).
% 0.19/0.40  fof(f74,plain,(
% 0.19/0.40    spl3_10),
% 0.19/0.40    inference(avatar_split_clause,[],[f29,f72])).
% 0.19/0.40  fof(f29,plain,(
% 0.19/0.40    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f15])).
% 0.19/0.40  fof(f15,plain,(
% 0.19/0.40    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.40    inference(ennf_transformation,[],[f8])).
% 0.19/0.40  fof(f8,plain,(
% 0.19/0.40    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.19/0.40    inference(unused_predicate_definition_removal,[],[f4])).
% 0.19/0.40  fof(f4,axiom,(
% 0.19/0.40    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.40  fof(f70,plain,(
% 0.19/0.40    spl3_9),
% 0.19/0.40    inference(avatar_split_clause,[],[f28,f68])).
% 0.19/0.40  fof(f28,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f14,plain,(
% 0.19/0.40    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.40    inference(ennf_transformation,[],[f3])).
% 0.19/0.40  fof(f3,axiom,(
% 0.19/0.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.19/0.40  fof(f66,plain,(
% 0.19/0.40    spl3_8),
% 0.19/0.40    inference(avatar_split_clause,[],[f27,f64])).
% 0.19/0.40  fof(f27,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f13])).
% 0.19/0.40  fof(f13,plain,(
% 0.19/0.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.40    inference(ennf_transformation,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.40  fof(f62,plain,(
% 0.19/0.40    spl3_7),
% 0.19/0.40    inference(avatar_split_clause,[],[f26,f60])).
% 0.19/0.40  fof(f26,plain,(
% 0.19/0.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f1])).
% 0.19/0.40  fof(f1,axiom,(
% 0.19/0.40    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.40  fof(f58,plain,(
% 0.19/0.40    spl3_6),
% 0.19/0.40    inference(avatar_split_clause,[],[f25,f56])).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f12])).
% 0.19/0.40  fof(f12,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.40    inference(flattening,[],[f11])).
% 0.19/0.40  fof(f11,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f5])).
% 0.19/0.40  fof(f5,axiom,(
% 0.19/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).
% 0.19/0.40  fof(f54,plain,(
% 0.19/0.40    spl3_5),
% 0.19/0.40    inference(avatar_split_clause,[],[f20,f51])).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    l1_pre_topc(sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f19])).
% 0.19/0.40  fof(f19,plain,(
% 0.19/0.40    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.19/0.40  fof(f16,plain,(
% 0.19/0.40    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f17,plain,(
% 0.19/0.40    ? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    ? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f10,plain,(
% 0.19/0.40    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.19/0.40    inference(flattening,[],[f9])).
% 0.19/0.40  fof(f9,plain,(
% 0.19/0.40    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f7])).
% 0.19/0.40  fof(f7,negated_conjecture,(
% 0.19/0.40    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.40    inference(negated_conjecture,[],[f6])).
% 0.19/0.40  fof(f6,conjecture,(
% 0.19/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tops_2)).
% 0.19/0.40  fof(f49,plain,(
% 0.19/0.40    spl3_4),
% 0.19/0.40    inference(avatar_split_clause,[],[f21,f46])).
% 0.19/0.40  fof(f21,plain,(
% 0.19/0.40    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    inference(cnf_transformation,[],[f19])).
% 0.19/0.40  fof(f44,plain,(
% 0.19/0.40    spl3_3),
% 0.19/0.40    inference(avatar_split_clause,[],[f22,f41])).
% 0.19/0.40  fof(f22,plain,(
% 0.19/0.40    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    inference(cnf_transformation,[],[f19])).
% 0.19/0.40  fof(f39,plain,(
% 0.19/0.40    spl3_2),
% 0.19/0.40    inference(avatar_split_clause,[],[f23,f36])).
% 0.19/0.40  fof(f23,plain,(
% 0.19/0.40    v1_tops_2(sK1,sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f19])).
% 0.19/0.40  fof(f34,plain,(
% 0.19/0.40    ~spl3_1),
% 0.19/0.40    inference(avatar_split_clause,[],[f24,f31])).
% 0.19/0.40  fof(f24,plain,(
% 0.19/0.40    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f19])).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (23961)------------------------------
% 0.19/0.40  % (23961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (23961)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (23961)Memory used [KB]: 6268
% 0.19/0.41  % (23961)Time elapsed: 0.008 s
% 0.19/0.41  % (23961)------------------------------
% 0.19/0.41  % (23961)------------------------------
% 0.19/0.41  % (23950)Success in time 0.062 s
%------------------------------------------------------------------------------
