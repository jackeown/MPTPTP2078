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
% DateTime   : Thu Dec  3 13:11:04 EST 2020

% Result     : Theorem 3.96s
% Output     : Refutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 283 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  353 ( 799 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f82,f120,f126,f145,f182,f191,f222,f225,f249,f469,f1442,f1551,f1885,f2392])).

fof(f2392,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_97 ),
    inference(avatar_contradiction_clause,[],[f2369])).

fof(f2369,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_97 ),
    inference(unit_resulting_resolution,[],[f69,f64,f59,f49,f1550,f59,f421,f271])).

fof(f271,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( r1_tarski(X21,k1_tops_1(X20,k2_xboole_0(X18,X19)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ l1_pre_topc(X20)
      | ~ r1_tarski(X17,k2_xboole_0(X18,X19))
      | ~ r1_tarski(X21,k1_tops_1(X20,X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(resolution,[],[f165,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f165,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | r1_tarski(X6,k1_tops_1(X5,X4))
      | ~ r1_tarski(X6,k1_tops_1(X5,X3)) ) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
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
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f421,plain,(
    ! [X8,X9] : r1_tarski(X8,k2_xboole_0(X9,X8)) ),
    inference(superposition,[],[f41,f186])).

fof(f186,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f84,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1550,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_97 ),
    inference(avatar_component_clause,[],[f1548])).

fof(f1548,plain,
    ( spl3_97
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1885,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_93 ),
    inference(avatar_contradiction_clause,[],[f1873])).

fof(f1873,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_93 ),
    inference(unit_resulting_resolution,[],[f69,f64,f59,f64,f41,f49,f1441,f271])).

fof(f1441,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_93 ),
    inference(avatar_component_clause,[],[f1439])).

fof(f1439,plain,
    ( spl3_93
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1551,plain,
    ( ~ spl3_97
    | spl3_50 ),
    inference(avatar_split_clause,[],[f1542,f462,f1548])).

fof(f462,plain,
    ( spl3_50
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1542,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_50 ),
    inference(resolution,[],[f464,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f464,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_50 ),
    inference(avatar_component_clause,[],[f462])).

fof(f1442,plain,
    ( ~ spl3_93
    | spl3_51 ),
    inference(avatar_split_clause,[],[f1433,f466,f1439])).

fof(f466,plain,
    ( spl3_51
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f1433,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_51 ),
    inference(resolution,[],[f468,f37])).

fof(f468,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f466])).

fof(f469,plain,
    ( ~ spl3_50
    | ~ spl3_51
    | spl3_22 ),
    inference(avatar_split_clause,[],[f444,f193,f466,f462])).

fof(f193,plain,
    ( spl3_22
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f444,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_22 ),
    inference(resolution,[],[f255,f195])).

fof(f195,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f193])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f127,f44])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f249,plain,
    ( ~ spl3_22
    | ~ spl3_2
    | ~ spl3_3
    | spl3_15 ),
    inference(avatar_split_clause,[],[f248,f142,f62,f57,f193])).

fof(f142,plain,
    ( spl3_15
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f248,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_15 ),
    inference(subsumption_resolution,[],[f247,f64])).

fof(f247,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_15 ),
    inference(subsumption_resolution,[],[f246,f59])).

fof(f246,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(superposition,[],[f144,f44])).

fof(f144,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f225,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f76,f119,f221,f35])).

fof(f221,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f119,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_11
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f76,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_5
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f222,plain,
    ( ~ spl3_26
    | spl3_14 ),
    inference(avatar_split_clause,[],[f217,f138,f219])).

fof(f138,plain,
    ( spl3_14
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f217,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_14 ),
    inference(resolution,[],[f140,f37])).

fof(f140,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f191,plain,
    ( ~ spl3_6
    | ~ spl3_12
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_12
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f81,f125,f181,f35])).

fof(f181,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_21
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f125,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f81,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f182,plain,
    ( ~ spl3_21
    | spl3_13 ),
    inference(avatar_split_clause,[],[f177,f134,f179])).

fof(f134,plain,
    ( spl3_13
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f177,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_13 ),
    inference(resolution,[],[f136,f37])).

fof(f136,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f145,plain,
    ( ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | spl3_1 ),
    inference(avatar_split_clause,[],[f129,f52,f142,f138,f134])).

fof(f52,plain,
    ( spl3_1
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f129,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f54,f44])).

fof(f54,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f126,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f121,f67,f62,f123])).

fof(f121,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f113,f69])).

fof(f113,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f43,f64])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f120,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f115,f67,f57,f117])).

fof(f115,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f112,f69])).

fof(f112,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f43,f59])).

fof(f82,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f72,f62,f79])).

fof(f72,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f36,f64])).

fof(f77,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f71,f57,f74])).

fof(f71,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f36,f59])).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:50:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (21452)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (21455)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (21444)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (21463)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.56  % (21440)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.56  % (21462)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.56  % (21448)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.57  % (21441)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.57  % (21460)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.57  % (21464)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.57  % (21443)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.61/0.57  % (21468)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.61/0.57  % (21447)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.61/0.57  % (21450)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.61/0.58  % (21451)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.61/0.58  % (21465)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.61/0.59  % (21457)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.61/0.59  % (21467)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.61/0.59  % (21459)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.61/0.59  % (21449)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.61/0.59  % (21454)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.61/0.59  % (21445)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.60  % (21442)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.61/0.60  % (21446)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.61  % (21456)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.61/0.61  % (21469)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.61/0.61  % (21466)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.61/0.61  % (21461)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.61/0.62  % (21458)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.61/0.62  % (21453)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 3.45/0.85  % (21442)Time limit reached!
% 3.45/0.85  % (21442)------------------------------
% 3.45/0.85  % (21442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.45/0.85  % (21442)Termination reason: Time limit
% 3.45/0.85  
% 3.45/0.85  % (21442)Memory used [KB]: 6140
% 3.45/0.85  % (21442)Time elapsed: 0.412 s
% 3.45/0.85  % (21442)------------------------------
% 3.45/0.85  % (21442)------------------------------
% 3.45/0.87  % (21464)Time limit reached!
% 3.45/0.87  % (21464)------------------------------
% 3.45/0.87  % (21464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.45/0.87  % (21464)Termination reason: Time limit
% 3.45/0.87  
% 3.45/0.87  % (21464)Memory used [KB]: 12281
% 3.45/0.87  % (21464)Time elapsed: 0.429 s
% 3.45/0.87  % (21464)------------------------------
% 3.45/0.87  % (21464)------------------------------
% 3.96/0.93  % (21469)Time limit reached!
% 3.96/0.93  % (21469)------------------------------
% 3.96/0.93  % (21469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.93  % (21469)Termination reason: Time limit
% 3.96/0.93  % (21469)Termination phase: Saturation
% 3.96/0.93  
% 3.96/0.93  % (21469)Memory used [KB]: 2686
% 3.96/0.93  % (21469)Time elapsed: 0.501 s
% 3.96/0.93  % (21469)------------------------------
% 3.96/0.93  % (21469)------------------------------
% 3.96/0.94  % (21461)Refutation found. Thanks to Tanya!
% 3.96/0.94  % SZS status Theorem for theBenchmark
% 3.96/0.95  % SZS output start Proof for theBenchmark
% 3.96/0.95  fof(f2399,plain,(
% 3.96/0.95    $false),
% 3.96/0.95    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f82,f120,f126,f145,f182,f191,f222,f225,f249,f469,f1442,f1551,f1885,f2392])).
% 3.96/0.95  fof(f2392,plain,(
% 3.96/0.95    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_97),
% 3.96/0.95    inference(avatar_contradiction_clause,[],[f2369])).
% 3.96/0.95  fof(f2369,plain,(
% 3.96/0.95    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_97)),
% 3.96/0.95    inference(unit_resulting_resolution,[],[f69,f64,f59,f49,f1550,f59,f421,f271])).
% 3.96/0.95  fof(f271,plain,(
% 3.96/0.95    ( ! [X21,X19,X17,X20,X18] : (r1_tarski(X21,k1_tops_1(X20,k2_xboole_0(X18,X19))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X20))) | ~l1_pre_topc(X20) | ~r1_tarski(X17,k2_xboole_0(X18,X19)) | ~r1_tarski(X21,k1_tops_1(X20,X17)) | ~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X20))) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X20)))) )),
% 3.96/0.95    inference(resolution,[],[f165,f132])).
% 3.96/0.95  fof(f132,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.95    inference(duplicate_literal_removal,[],[f131])).
% 3.96/0.95  fof(f131,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.95    inference(superposition,[],[f45,f44])).
% 3.96/0.95  fof(f44,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.95    inference(cnf_transformation,[],[f21])).
% 3.96/0.95  fof(f21,plain,(
% 3.96/0.95    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.95    inference(flattening,[],[f20])).
% 3.96/0.95  fof(f20,plain,(
% 3.96/0.95    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.96/0.95    inference(ennf_transformation,[],[f8])).
% 3.96/0.95  fof(f8,axiom,(
% 3.96/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.96/0.95  fof(f45,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.95    inference(cnf_transformation,[],[f23])).
% 3.96/0.95  fof(f23,plain,(
% 3.96/0.95    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.95    inference(flattening,[],[f22])).
% 3.96/0.95  fof(f22,plain,(
% 3.96/0.95    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.96/0.95    inference(ennf_transformation,[],[f7])).
% 3.96/0.95  fof(f7,axiom,(
% 3.96/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.96/0.95  fof(f165,plain,(
% 3.96/0.95    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | ~r1_tarski(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | r1_tarski(X6,k1_tops_1(X5,X4)) | ~r1_tarski(X6,k1_tops_1(X5,X3))) )),
% 3.96/0.95    inference(resolution,[],[f42,f35])).
% 3.96/0.95  fof(f35,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.96/0.95    inference(cnf_transformation,[],[f16])).
% 3.96/0.95  fof(f16,plain,(
% 3.96/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.96/0.95    inference(flattening,[],[f15])).
% 3.96/0.95  fof(f15,plain,(
% 3.96/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.96/0.95    inference(ennf_transformation,[],[f2])).
% 3.96/0.95  fof(f2,axiom,(
% 3.96/0.95    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.96/0.95  fof(f42,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.95    inference(cnf_transformation,[],[f18])).
% 3.96/0.95  fof(f18,plain,(
% 3.96/0.95    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.95    inference(flattening,[],[f17])).
% 3.96/0.95  fof(f17,plain,(
% 3.96/0.95    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.95    inference(ennf_transformation,[],[f11])).
% 3.96/0.95  fof(f11,axiom,(
% 3.96/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 3.96/0.95  fof(f421,plain,(
% 3.96/0.95    ( ! [X8,X9] : (r1_tarski(X8,k2_xboole_0(X9,X8))) )),
% 3.96/0.95    inference(superposition,[],[f41,f186])).
% 3.96/0.95  fof(f186,plain,(
% 3.96/0.95    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 3.96/0.95    inference(superposition,[],[f84,f47])).
% 3.96/0.95  fof(f47,plain,(
% 3.96/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.96/0.95    inference(cnf_transformation,[],[f6])).
% 3.96/0.95  fof(f6,axiom,(
% 3.96/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.96/0.95  fof(f84,plain,(
% 3.96/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 3.96/0.95    inference(superposition,[],[f47,f48])).
% 3.96/0.95  fof(f48,plain,(
% 3.96/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.96/0.95    inference(cnf_transformation,[],[f4])).
% 3.96/0.95  fof(f4,axiom,(
% 3.96/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.96/0.95  fof(f41,plain,(
% 3.96/0.95    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.96/0.95    inference(cnf_transformation,[],[f3])).
% 3.96/0.95  fof(f3,axiom,(
% 3.96/0.95    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.96/0.95  fof(f1550,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_97),
% 3.96/0.95    inference(avatar_component_clause,[],[f1548])).
% 3.96/0.95  fof(f1548,plain,(
% 3.96/0.95    spl3_97 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 3.96/0.95  fof(f49,plain,(
% 3.96/0.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.96/0.95    inference(equality_resolution,[],[f39])).
% 3.96/0.95  fof(f39,plain,(
% 3.96/0.95    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.96/0.95    inference(cnf_transformation,[],[f30])).
% 3.96/0.95  fof(f30,plain,(
% 3.96/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.96/0.95    inference(flattening,[],[f29])).
% 3.96/0.95  fof(f29,plain,(
% 3.96/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.96/0.95    inference(nnf_transformation,[],[f1])).
% 3.96/0.95  fof(f1,axiom,(
% 3.96/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.96/0.95  fof(f59,plain,(
% 3.96/0.95    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 3.96/0.95    inference(avatar_component_clause,[],[f57])).
% 3.96/0.95  fof(f57,plain,(
% 3.96/0.95    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.96/0.95  fof(f64,plain,(
% 3.96/0.95    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 3.96/0.95    inference(avatar_component_clause,[],[f62])).
% 3.96/0.95  fof(f62,plain,(
% 3.96/0.95    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.96/0.95  fof(f69,plain,(
% 3.96/0.95    l1_pre_topc(sK0) | ~spl3_4),
% 3.96/0.95    inference(avatar_component_clause,[],[f67])).
% 3.96/0.95  fof(f67,plain,(
% 3.96/0.95    spl3_4 <=> l1_pre_topc(sK0)),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.96/0.95  fof(f1885,plain,(
% 3.96/0.95    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_93),
% 3.96/0.95    inference(avatar_contradiction_clause,[],[f1873])).
% 3.96/0.95  fof(f1873,plain,(
% 3.96/0.95    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_93)),
% 3.96/0.95    inference(unit_resulting_resolution,[],[f69,f64,f59,f64,f41,f49,f1441,f271])).
% 3.96/0.95  fof(f1441,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_93),
% 3.96/0.95    inference(avatar_component_clause,[],[f1439])).
% 3.96/0.95  fof(f1439,plain,(
% 3.96/0.95    spl3_93 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 3.96/0.95  fof(f1551,plain,(
% 3.96/0.95    ~spl3_97 | spl3_50),
% 3.96/0.95    inference(avatar_split_clause,[],[f1542,f462,f1548])).
% 3.96/0.95  fof(f462,plain,(
% 3.96/0.95    spl3_50 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 3.96/0.95  fof(f1542,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_50),
% 3.96/0.95    inference(resolution,[],[f464,f37])).
% 3.96/0.95  fof(f37,plain,(
% 3.96/0.95    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.96/0.95    inference(cnf_transformation,[],[f28])).
% 3.96/0.95  fof(f28,plain,(
% 3.96/0.95    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.96/0.95    inference(nnf_transformation,[],[f9])).
% 3.96/0.95  fof(f9,axiom,(
% 3.96/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.96/0.95  fof(f464,plain,(
% 3.96/0.95    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_50),
% 3.96/0.95    inference(avatar_component_clause,[],[f462])).
% 3.96/0.95  fof(f1442,plain,(
% 3.96/0.95    ~spl3_93 | spl3_51),
% 3.96/0.95    inference(avatar_split_clause,[],[f1433,f466,f1439])).
% 3.96/0.95  fof(f466,plain,(
% 3.96/0.95    spl3_51 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 3.96/0.95  fof(f1433,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_51),
% 3.96/0.95    inference(resolution,[],[f468,f37])).
% 3.96/0.95  fof(f468,plain,(
% 3.96/0.95    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_51),
% 3.96/0.95    inference(avatar_component_clause,[],[f466])).
% 3.96/0.95  fof(f469,plain,(
% 3.96/0.95    ~spl3_50 | ~spl3_51 | spl3_22),
% 3.96/0.95    inference(avatar_split_clause,[],[f444,f193,f466,f462])).
% 3.96/0.95  fof(f193,plain,(
% 3.96/0.95    spl3_22 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 3.96/0.95  fof(f444,plain,(
% 3.96/0.95    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_22),
% 3.96/0.95    inference(resolution,[],[f255,f195])).
% 3.96/0.95  fof(f195,plain,(
% 3.96/0.95    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_22),
% 3.96/0.95    inference(avatar_component_clause,[],[f193])).
% 3.96/0.95  fof(f255,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.96/0.95    inference(duplicate_literal_removal,[],[f254])).
% 3.96/0.95  fof(f254,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.95    inference(superposition,[],[f127,f44])).
% 3.96/0.95  fof(f127,plain,(
% 3.96/0.95    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.96/0.95    inference(resolution,[],[f45,f36])).
% 3.96/0.95  fof(f36,plain,(
% 3.96/0.95    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.96/0.95    inference(cnf_transformation,[],[f28])).
% 3.96/0.95  fof(f249,plain,(
% 3.96/0.95    ~spl3_22 | ~spl3_2 | ~spl3_3 | spl3_15),
% 3.96/0.95    inference(avatar_split_clause,[],[f248,f142,f62,f57,f193])).
% 3.96/0.95  fof(f142,plain,(
% 3.96/0.95    spl3_15 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 3.96/0.95  fof(f248,plain,(
% 3.96/0.95    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_15)),
% 3.96/0.95    inference(subsumption_resolution,[],[f247,f64])).
% 3.96/0.95  fof(f247,plain,(
% 3.96/0.95    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_15)),
% 3.96/0.95    inference(subsumption_resolution,[],[f246,f59])).
% 3.96/0.95  fof(f246,plain,(
% 3.96/0.95    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 3.96/0.95    inference(superposition,[],[f144,f44])).
% 3.96/0.95  fof(f144,plain,(
% 3.96/0.95    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_15),
% 3.96/0.95    inference(avatar_component_clause,[],[f142])).
% 3.96/0.95  fof(f225,plain,(
% 3.96/0.95    ~spl3_5 | ~spl3_11 | spl3_26),
% 3.96/0.95    inference(avatar_contradiction_clause,[],[f224])).
% 3.96/0.95  fof(f224,plain,(
% 3.96/0.95    $false | (~spl3_5 | ~spl3_11 | spl3_26)),
% 3.96/0.95    inference(unit_resulting_resolution,[],[f76,f119,f221,f35])).
% 3.96/0.95  fof(f221,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_26),
% 3.96/0.95    inference(avatar_component_clause,[],[f219])).
% 3.96/0.95  fof(f219,plain,(
% 3.96/0.95    spl3_26 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 3.96/0.95  fof(f119,plain,(
% 3.96/0.95    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_11),
% 3.96/0.95    inference(avatar_component_clause,[],[f117])).
% 3.96/0.95  fof(f117,plain,(
% 3.96/0.95    spl3_11 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 3.96/0.95  fof(f76,plain,(
% 3.96/0.95    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_5),
% 3.96/0.95    inference(avatar_component_clause,[],[f74])).
% 3.96/0.95  fof(f74,plain,(
% 3.96/0.95    spl3_5 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.96/0.95  fof(f222,plain,(
% 3.96/0.95    ~spl3_26 | spl3_14),
% 3.96/0.95    inference(avatar_split_clause,[],[f217,f138,f219])).
% 3.96/0.95  fof(f138,plain,(
% 3.96/0.95    spl3_14 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 3.96/0.95  fof(f217,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_14),
% 3.96/0.95    inference(resolution,[],[f140,f37])).
% 3.96/0.95  fof(f140,plain,(
% 3.96/0.95    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_14),
% 3.96/0.95    inference(avatar_component_clause,[],[f138])).
% 3.96/0.95  fof(f191,plain,(
% 3.96/0.95    ~spl3_6 | ~spl3_12 | spl3_21),
% 3.96/0.95    inference(avatar_contradiction_clause,[],[f190])).
% 3.96/0.95  fof(f190,plain,(
% 3.96/0.95    $false | (~spl3_6 | ~spl3_12 | spl3_21)),
% 3.96/0.95    inference(unit_resulting_resolution,[],[f81,f125,f181,f35])).
% 3.96/0.95  fof(f181,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_21),
% 3.96/0.95    inference(avatar_component_clause,[],[f179])).
% 3.96/0.95  fof(f179,plain,(
% 3.96/0.95    spl3_21 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 3.96/0.95  fof(f125,plain,(
% 3.96/0.95    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 3.96/0.95    inference(avatar_component_clause,[],[f123])).
% 3.96/0.95  fof(f123,plain,(
% 3.96/0.95    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 3.96/0.95  fof(f81,plain,(
% 3.96/0.95    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 3.96/0.95    inference(avatar_component_clause,[],[f79])).
% 3.96/0.95  fof(f79,plain,(
% 3.96/0.95    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.96/0.95  fof(f182,plain,(
% 3.96/0.95    ~spl3_21 | spl3_13),
% 3.96/0.95    inference(avatar_split_clause,[],[f177,f134,f179])).
% 3.96/0.95  fof(f134,plain,(
% 3.96/0.95    spl3_13 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.96/0.95  fof(f177,plain,(
% 3.96/0.95    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_13),
% 3.96/0.95    inference(resolution,[],[f136,f37])).
% 3.96/0.95  fof(f136,plain,(
% 3.96/0.95    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_13),
% 3.96/0.95    inference(avatar_component_clause,[],[f134])).
% 3.96/0.95  fof(f145,plain,(
% 3.96/0.95    ~spl3_13 | ~spl3_14 | ~spl3_15 | spl3_1),
% 3.96/0.95    inference(avatar_split_clause,[],[f129,f52,f142,f138,f134])).
% 3.96/0.95  fof(f52,plain,(
% 3.96/0.95    spl3_1 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 3.96/0.95    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.96/0.95  fof(f129,plain,(
% 3.96/0.95    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 3.96/0.95    inference(superposition,[],[f54,f44])).
% 3.96/0.95  fof(f54,plain,(
% 3.96/0.95    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_1),
% 3.96/0.95    inference(avatar_component_clause,[],[f52])).
% 3.96/0.95  fof(f126,plain,(
% 3.96/0.95    spl3_12 | ~spl3_3 | ~spl3_4),
% 3.96/0.95    inference(avatar_split_clause,[],[f121,f67,f62,f123])).
% 3.96/0.95  fof(f121,plain,(
% 3.96/0.95    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 3.96/0.95    inference(subsumption_resolution,[],[f113,f69])).
% 3.96/0.95  fof(f113,plain,(
% 3.96/0.95    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.96/0.95    inference(resolution,[],[f43,f64])).
% 3.96/0.95  fof(f43,plain,(
% 3.96/0.95    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.96/0.95    inference(cnf_transformation,[],[f19])).
% 3.96/0.95  fof(f19,plain,(
% 3.96/0.95    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.95    inference(ennf_transformation,[],[f10])).
% 3.96/0.95  fof(f10,axiom,(
% 3.96/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 3.96/0.95  fof(f120,plain,(
% 3.96/0.95    spl3_11 | ~spl3_2 | ~spl3_4),
% 3.96/0.95    inference(avatar_split_clause,[],[f115,f67,f57,f117])).
% 3.96/0.95  fof(f115,plain,(
% 3.96/0.95    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_4)),
% 3.96/0.95    inference(subsumption_resolution,[],[f112,f69])).
% 3.96/0.95  fof(f112,plain,(
% 3.96/0.95    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0) | ~spl3_2),
% 3.96/0.95    inference(resolution,[],[f43,f59])).
% 3.96/0.95  fof(f82,plain,(
% 3.96/0.95    spl3_6 | ~spl3_3),
% 3.96/0.95    inference(avatar_split_clause,[],[f72,f62,f79])).
% 3.96/0.95  fof(f72,plain,(
% 3.96/0.95    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 3.96/0.95    inference(resolution,[],[f36,f64])).
% 3.96/0.95  fof(f77,plain,(
% 3.96/0.95    spl3_5 | ~spl3_2),
% 3.96/0.95    inference(avatar_split_clause,[],[f71,f57,f74])).
% 3.96/0.95  fof(f71,plain,(
% 3.96/0.95    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_2),
% 3.96/0.95    inference(resolution,[],[f36,f59])).
% 3.96/0.95  fof(f70,plain,(
% 3.96/0.95    spl3_4),
% 3.96/0.95    inference(avatar_split_clause,[],[f31,f67])).
% 3.96/0.95  fof(f31,plain,(
% 3.96/0.95    l1_pre_topc(sK0)),
% 3.96/0.95    inference(cnf_transformation,[],[f27])).
% 3.96/0.95  fof(f27,plain,(
% 3.96/0.95    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.96/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 3.96/0.95  fof(f24,plain,(
% 3.96/0.95    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.96/0.95    introduced(choice_axiom,[])).
% 3.96/0.95  fof(f25,plain,(
% 3.96/0.95    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.96/0.95    introduced(choice_axiom,[])).
% 3.96/0.95  fof(f26,plain,(
% 3.96/0.95    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.96/0.95    introduced(choice_axiom,[])).
% 3.96/0.95  fof(f14,plain,(
% 3.96/0.95    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.96/0.95    inference(ennf_transformation,[],[f13])).
% 3.96/0.95  fof(f13,negated_conjecture,(
% 3.96/0.95    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.96/0.95    inference(negated_conjecture,[],[f12])).
% 3.96/0.95  fof(f12,conjecture,(
% 3.96/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.96/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 3.96/0.95  fof(f65,plain,(
% 3.96/0.95    spl3_3),
% 3.96/0.95    inference(avatar_split_clause,[],[f32,f62])).
% 3.96/0.95  fof(f32,plain,(
% 3.96/0.95    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.95    inference(cnf_transformation,[],[f27])).
% 3.96/0.95  fof(f60,plain,(
% 3.96/0.95    spl3_2),
% 3.96/0.95    inference(avatar_split_clause,[],[f33,f57])).
% 3.96/0.95  fof(f33,plain,(
% 3.96/0.95    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.95    inference(cnf_transformation,[],[f27])).
% 3.96/0.95  fof(f55,plain,(
% 3.96/0.95    ~spl3_1),
% 3.96/0.95    inference(avatar_split_clause,[],[f34,f52])).
% 3.96/0.95  fof(f34,plain,(
% 3.96/0.95    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 3.96/0.95    inference(cnf_transformation,[],[f27])).
% 3.96/0.95  % SZS output end Proof for theBenchmark
% 3.96/0.95  % (21461)------------------------------
% 3.96/0.95  % (21461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.95  % (21461)Termination reason: Refutation
% 3.96/0.95  
% 3.96/0.95  % (21461)Memory used [KB]: 7803
% 3.96/0.95  % (21461)Time elapsed: 0.520 s
% 3.96/0.95  % (21461)------------------------------
% 3.96/0.95  % (21461)------------------------------
% 3.96/0.96  % (21439)Success in time 0.582 s
%------------------------------------------------------------------------------
